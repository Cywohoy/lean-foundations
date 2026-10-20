// Static experiment server. There is no compiler process or proof submission endpoint.
const fs = require('node:fs');
const fsp = require('node:fs/promises');
const http = require('node:http');
const path = require('node:path');
const upstream = path.resolve(__dirname, '../../tmp/wasm/upstream');
const artifacts = path.resolve(process.env.LEAN_WASM_ARTIFACTS || path.join(upstream, 'tests/.artifacts'));
const ample = path.resolve(__dirname, '../../../Ample');
const overlay = process.env.AMPLE_WASM_LIBRARY ? path.resolve(process.env.AMPLE_WASM_LIBRARY) : null;
const packRoot = process.env.LEAN_WASM_PACKS ? path.resolve(process.env.LEAN_WASM_PACKS) : null;

function listFiles(root, relative = '') {
  return fs.readdirSync(path.join(root, relative), {withFileTypes: true}).flatMap(entry => {
    const name = relative ? `${relative}/${entry.name}` : entry.name;
    return entry.isDirectory() ? listFiles(root, name)
      : /\.(olean|ir|ir\.sig)$/.test(name) ? [name] : [];
  });
}

async function createServer({isolate = true, basePath = '/'} = {}) {
  if (!/^\/(?:[A-Za-z0-9_-]+\/)*$/.test(basePath)) throw new Error('Use an absolute directory path for basePath');
  const lib = path.join(artifacts, 'lib/lean');
  const nativeModule = path.join(ample, '.lake/build/lib/lean/Ample/Tactic/Classical.olean');
  const packed = packRoot ? JSON.parse(await fsp.readFile(path.join(packRoot, 'library.json'), 'utf8')) : null;
  const manifest = packed ? packed.files : [...new Set([...listFiles(lib), ...(overlay ? listFiles(overlay) : [])])];
  // The old baseline deliberately probes rejection of a native, mismatched olean.
  const probeNative = !overlay && !fs.existsSync(path.join(lib, 'Ample/Tactic/Classical.olean'));
  if (probeNative && fs.existsSync(nativeModule)) manifest.push('Ample/Tactic/Classical.olean');
  const mime = {'.html': 'text/html; charset=utf-8', '.js': 'text/javascript', '.wasm': 'application/wasm'};
  const server = http.createServer(async (req, res) => {
    try {
      if (isolate) {
        res.setHeader('Cross-Origin-Opener-Policy', 'same-origin');
        res.setHeader('Cross-Origin-Embedder-Policy', 'require-corp');
      }
      const pathname = decodeURIComponent(new URL(req.url, 'http://localhost').pathname);
      if (pathname === '/favicon.ico') { res.writeHead(204).end(); return; }
      if (!pathname.startsWith(basePath)) { res.writeHead(404).end(); return; }
      const route = '/' + pathname.slice(basePath.length);
      if (route === '/favicon.ico') { res.writeHead(204).end(); return; }
      if (route === '/library.json') {
        res.writeHead(200, {'Content-Type': 'application/json'}).end(JSON.stringify(packed || manifest)); return;
      }
      if (route === '/runtime.json') {
        const header = path.join(artifacts, 'include/lean/version.h');
        const text = fs.existsSync(header) ? await fsp.readFile(header, 'utf8') : '';
        const version = /#define LEAN_VERSION_STRING "([^"]+)"/.exec(text)?.[1]
          || (process.env.LEAN_WASM_ARTIFACTS ? 'unknown' : '4.33 (pinned fixture)');
        res.writeHead(200, {'Content-Type': 'application/json'}).end(JSON.stringify({version})); return;
      }
      let root = __dirname;
      let relative = route.slice(1) || 'index.html';
      if (route === '/lean-wasm.js') { root = path.resolve(__dirname, '../../assets/web'); relative = 'lean-wasm.js'; }
      if (route === '/upstream-worker.js') { root = path.join(upstream, 'public'); relative = 'lean-worker-persistent.worker.js'; }
      else if (route === '/coi-serviceworker.js') { root = path.resolve(upstream, '../coi-serviceworker'); relative = 'coi-serviceworker.js'; }
      else if (route.startsWith('/runtime/')) {
        root = process.env.LEAN_WASM_RUNTIME ? path.resolve(process.env.LEAN_WASM_RUNTIME)
          : path.join(artifacts, fs.existsSync(path.join(artifacts, 'runtime/lean.js')) ? 'runtime' : 'bin'); relative = route.slice(9);
      }
      else if (packRoot && route.startsWith('/packs/')) {
        root = fs.existsSync(path.join(packRoot, 'packs')) ? path.join(packRoot, 'packs') : packRoot;
        relative = route.slice(7);
      }
      else if (probeNative && route === '/library/Ample/Tactic/Classical.olean') {
        root = path.dirname(nativeModule); relative = path.basename(nativeModule);
      } else if (route.startsWith('/library/')) {
        relative = route.slice(9);
        root = overlay && fs.existsSync(path.join(overlay, relative)) ? overlay : lib;
      }
      const filename = path.resolve(root, relative);
      if (!filename.startsWith(path.resolve(root) + path.sep)) { res.writeHead(403).end(); return; }
      const stat = await fsp.stat(filename);
      res.writeHead(200, {'Content-Type': mime[path.extname(filename)] || 'application/octet-stream', 'Content-Length': stat.size});
      fs.createReadStream(filename).pipe(res);
    } catch { if (!res.headersSent) res.writeHead(404); res.end(); }
  });
  await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
  return server;
}

module.exports = {createServer, upstream, artifacts, ample};
if (require.main === module) createServer().then(server => console.log(`Experiment: http://127.0.0.1:${server.address().port}/`));
