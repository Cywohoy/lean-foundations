/** Browser-only Lean compiler transport. Proofs remain inside its Worker. */
export function createLeanRuntime(baseURL, onProgress = () => {}) {
  const base = new URL(baseURL);
  let worker;
  let pending;
  let output = [];
  let libraryManifest = [];
  let libraryPacks = [];
  let ready = false;
  const runtimeProfile = [];
  const loadedFiles = new Set();
  // Lean retains imported compact regions for the lifetime of the worker.
  // Bound distinct environments, including partial contexts on a continuous page.
  const importSets = new Set();
  const contextFiles = new Map();
  const maxImportSets = 4;
  function request(message, expected, timeout = 180000, transfer = []) {
    if (pending) throw new Error('A compiler operation is already running');
    output = [];
    return new Promise((resolve, reject) => {
      const timer = setTimeout(() => {
        pending = null;
        worker.terminate();
        reject(new Error(`Timed out waiting for ${expected}; reload to restart`));
      }, timeout);
      pending = { expected, resolve, reject, timer };
      worker.postMessage(message, transfer);
    });
  }

  async function boot() {
    if (worker) throw new Error('Reload the page before starting another runtime');
    if (!crossOriginIsolated) throw new Error('Cross-origin isolation is required by this runtime');
    try {
      const started = performance.now();
      const timings = [];
      const mark = stage => timings.push({stage, elapsedMs: performance.now() - started});
      onProgress('Loading runtime and library…');
      worker = new Worker(new URL('worker.js?assetBase=runtime', base));
      worker.onmessage = ({data}) => {
        if (data.type === 'profile') runtimeProfile.push(data);
        if (data.type === 'stdout' || data.type === 'stderr') output.push(data.data);
        if (data.type === 'import_progress') onProgress(`Loading modules: ${data.loaded}/${data.total}`);
        if (pending && (data.type === pending.expected || data.type === 'error')) {
          const current = pending;
          pending = null;
          clearTimeout(current.timer);
          if (data.type === 'error') current.reject(new Error(data.data));
          else current.resolve({...data, output: [...output]});
        }
      };
      worker.onerror = event => {
        if (pending) {
          clearTimeout(pending.timer);
          pending.reject(new Error(event.message));
          pending = null;
        }
      };
      const manifest = await (await fetch(new URL('library.json', base))).json();
      mark('manifest');
      libraryManifest = Array.isArray(manifest) ? manifest : manifest.files;
      libraryPacks = manifest.packs || [];
      const files = await fetchLibrary(libraryManifest.filter(name => name === 'Init.olean' || name.startsWith('Init/')));
      mark('initial-library-fetched');
      await request({type: 'load_library', files}, 'library_received', 180000, files.map(file => file.data));
      files.forEach(file => loadedFiles.add(file.name));
      await request({type: 'start_worker'}, 'worker_ready');
      mark('runtime-ready');
      // Measure the first import separately from later editing cycles.
      const warmup = await compile('#check Nat');
      mark('initial-import');
      if (!warmup.success) throw new Error(JSON.stringify(warmup));
      onProgress('Ready');
      ready = true;
      return {bootMs: performance.now() - started, libraryFiles: files.length, warmup, timings, runtimeProfile};
    } catch (error) {
      // A failed boot must be restartable, without retaining a partial worker.
      worker?.terminate();
      worker = undefined;
      ready = false;
      loadedFiles.clear();
      importSets.clear();
      throw error;
    }
  }

  async function fetchLibrary(manifest) {
    if (libraryPacks.length) return fetchPackedLibrary(manifest);
    const files = [];
    let next = 0;
    await Promise.all(Array.from({length: 16}, async () => {
      while (next < manifest.length) {
        const name = manifest[next++];
        const response = await fetch(new URL(`library/${name}`, base));
        if (!response.ok) throw new Error(`Cannot load ${name}: ${response.status}`);
        files.push({name, data: await response.arrayBuffer()});
      }
    }));
    return files;
  }

  async function fetchPackedLibrary(manifest) {
    const wanted = new Set(manifest);
    const packs = libraryPacks.filter(pack => pack.entries.some(entry => wanted.has(entry.path)));
    const files = [];
    let next = 0;
    let finished = 0;
    await Promise.all(Array.from({length: 2}, async () => {
      while (next < packs.length) {
        const pack = packs[next++];
        const response = await fetch(new URL(`packs/${pack.file}`, base));
        if (!response.ok) throw new Error(`Cannot load ${pack.file}: ${response.status}`);
        const compressed = await response.arrayBuffer();
        const digest = [...new Uint8Array(await crypto.subtle.digest('SHA-256', compressed))]
          .map(byte => byte.toString(16).padStart(2, '0')).join('');
        if (compressed.byteLength !== pack.bytes || digest !== pack.sha256) throw new Error(`Corrupt library pack: ${pack.file}`);
        const raw = await new Response(new Blob([compressed]).stream().pipeThrough(new DecompressionStream('gzip'))).arrayBuffer();
        if (raw.byteLength !== pack.rawBytes) throw new Error(`Invalid decoded size: ${pack.file}`);
        for (const entry of pack.entries) if (wanted.has(entry.path)) {
          if (entry.offset < 0 || entry.offset + entry.bytes > raw.byteLength) throw new Error(`Invalid pack entry: ${entry.path}`);
          files.push({name: entry.path, data: raw.slice(entry.offset, entry.offset + entry.bytes)});
        }
        onProgress(`Loading library packs: ${++finished}/${packs.length}`);
      }
    }));
    if (files.length !== manifest.length) throw new Error('The library pack index is incomplete');
    return files;
  }

  async function compile(code) {
    const started = performance.now();
    const imports = code.match(/^(?:(?:public|meta)\s+)*import\s[^\n]*/gm);
    if (imports) {
      const signature = imports.join('\n');
      if (ready && !importSets.has(signature) && importSets.size >= maxImportSets) {
        if (pending) throw new Error('Cannot replace a busy compiler');
        worker.terminate();
        worker = undefined;
        ready = false;
        loadedFiles.clear();
        importSets.clear();
        runtimeProfile.length = 0;
        await boot();
        // addFiles transfers its input buffers; retain independent copies for reuse.
        await addFiles([...contextFiles].map(([name, data]) => ({name, data: data.slice(0)})));
      }
      importSets.add(signature);
      const additional = libraryManifest.filter(name => !loadedFiles.has(name));
      if (additional.length) {
        onProgress('Loading additional libraries…');
        const files = await fetchLibrary(additional);
        const staged = await request({type: 'add_files', files}, 'files_added', 180000, files.map(file => file.data));
        if (staged.count !== files.length) throw new Error('Not all requested library files could be staged');
        // Fetching a batch can fail after another pack has finished. Commit the
        // loaded set only when this complete batch reaches the worker.
        files.forEach(file => loadedFiles.add(file.name));
      }
    }
    const libraryMs = performance.now() - started;
    const result = await request({type: 'compile', code, path: '/workspace/Experiment.lean'}, 'compile_result');
    return {...result, wallMs: performance.now() - started, libraryMs};
  }

  async function goalsAt(line, character) {
    const result = await request({type: 'goals', line, character}, 'goals_result');
    if (!result.success) throw new Error([...result.output, result.error].join('\n'));
    for (const line of result.output) {
      try {
        const data = JSON.parse(line);
        if (typeof data.found === 'boolean' && Array.isArray(data.goals)) return data;
      } catch {}
    }
    throw new Error('Lean returned no goal response');
  }
  async function addFiles(files) {
    const missing = files.filter(file => !loadedFiles.has(file.name));
    if (!missing.length) return;
    for (const file of missing) contextFiles.set(file.name, file.data.slice(0));
    const result = await request({type: 'add_files', files: missing}, 'files_added', 180000, missing.map(file => file.data));
    if (result.count !== missing.length) throw new Error('Not all context files could be staged');
    missing.forEach(file => loadedFiles.add(file.name));
  }
  return {boot, compile, goalsAt, addFiles, get pending() { return !!pending; }, get ready() { return ready; }};
}
