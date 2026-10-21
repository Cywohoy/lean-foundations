import {createLeanRuntime} from './lean-wasm.js';

// Keep the reader's request/response contract; execution stays in one Worker.
export function createBrowserBackend(siteRoot) {
  const runtime = createLeanRuntime(new URL(document.querySelector('meta[name="lean-wasm-base"]').content, siteRoot), message => {
    const count = /Loading library packs: (\d+\/\d+)/.exec(message)?.[1];
    window.dispatchEvent(new CustomEvent('book-lean-progress', {
      detail: count ? `Lean 파일을 불러오는 중 (${count})…` : 'Lean을 준비하는 중…',
    }));
  });
  let boot;
  let queue = Promise.resolve();
  let currentSource;
  let currentResult;
  let serial = 0;
  const sessions = new Map();
  const snippets = new Map();
  const loadedContexts = new Set();

  async function isolate(key) {
    if (crossOriginIsolated) return;
    if (!isSecureContext || !navigator.serviceWorker) {
      throw new Error('이 브라우저에서는 Lean을 실행할 수 없습니다. 최신 데스크톱 Chrome 또는 Firefox를 사용해 주세요.');
    }
    sessionStorage.setItem('lean-algebra.reopen', key);
    let reloading = false;
    window.coi = {async doReload() {
      if (reloading) return;
      reloading = true;
      const registration = await navigator.serviceWorker.ready;
      const worker = registration.active;
      if (worker.state !== 'activated') await new Promise(resolve => worker.addEventListener('statechange', () => {
        if (worker.state === 'activated') resolve();
      }));
      location.reload();
    }};
    await new Promise((_, reject) => {
      const script = document.createElement('script');
      script.src = new URL('coi-serviceworker.js', siteRoot);
      script.onload = () => window.coi.doReload().catch(reject);
      script.onerror = () => reject(new Error('Lean 실행 환경을 불러오지 못했습니다. 페이지를 새로고침해 주세요.'));
      document.head.append(script);
      setTimeout(() => reject(new Error('Lean 실행 환경을 준비하지 못했습니다. 페이지를 새로고침해 주세요.')), 30000);
    });
  }
  function closeScopes(source) {
    const scopes = [];
    for (const line of source.split('\n')) {
      const open = /^(?:namespace|section)(?:\s+(\S+))?\s*$/.exec(line);
      if (open) scopes.push(open[1] || '');
      else if (/^end(?:\s+\S+)?\s*$/.test(line)) scopes.pop();
    }
    return '\n' + scopes.reverse().map(name => `end${name ? ' ' + name : ''}\n`).join('');
  }
  async function compile(document) {
    if (currentSource === document.source) return currentResult;
    const result = await runtime.compile(document.source);
    if (!result.success) throw new Error('Lean 실행이 중단되었습니다. 페이지를 새로고침해 주세요.');
    currentSource = document.source;
    currentResult = result;
    document.result = result;
    return result;
  }
  async function goals(document, position, range) {
    await compile(document);
    const state = await runtime.goalsAt(document.offset + position.line, position.character);
    if (state.found) return {goal: state.goals};
    // Parser recovery may leave no info tree at a malformed line. Use Lean's
    // unsolved-goal messages from this exact declaration, never a stale state.
    if (range && Number.isSafeInteger(range.startLine) && Number.isSafeInteger(range.endLine)) {
      const unfinished = (document.unsolved || []).filter(item =>
        item.line >= range.startLine && item.line <= range.endLine);
      if (unfinished.length) return {goal: [...new Set(unfinished.map(item => item.text))],
        goalNote: '오류가 난 증명의 남은 목표'};
    }
    return {goal: null};
  }
  async function execute(path, payload) {
    if (path === '/api/lean/check') {
      await isolate(payload.snippet);
      boot ||= runtime.boot();
      await boot;
      if (!snippets.has(payload.snippet)) {
        const response = await fetch(new URL(`playground/${payload.snippet}.json`, siteRoot));
        if (!response.ok) throw new Error('예제의 실행 환경을 불러오지 못했습니다.');
        snippets.set(payload.snippet, await response.json());
      }
      const snippet = snippets.get(payload.snippet);
      const files = [];
      for (const item of snippet.contextFiles || []) {
        if (loadedContexts.has(item.sha256)) continue;
        const response = await fetch(new URL(item.url, siteRoot));
        if (!response.ok) throw new Error('검사 문맥을 불러오지 못했습니다.');
        const data = await response.arrayBuffer();
        const digest = [...new Uint8Array(await crypto.subtle.digest('SHA-256', data))]
          .map(byte => byte.toString(16).padStart(2, '0')).join('');
        if (data.byteLength !== item.bytes || digest !== item.sha256) throw new Error('The checked exercise context is corrupt.');
        files.push({name: item.name, data});
      }
      await runtime.addFiles(files);
      for (const item of snippet.contextFiles || []) loadedContexts.add(item.sha256);
      const prefix = snippet.before.trimEnd() + '\n\n';
      const token = sessions.has(payload.session) ? payload.session : `wasm-${++serial}`;
      const previous = sessions.get(token);
      // Put the guard on the declaration's existing header line, preserving all
      // editable proof line/column positions for goals and diagnostics.
      const checkedCode = snippet.exercise && snippet.allowedTactics
        ? payload.code.replace(/^((?:theorem|lemma|example)\b[\s\S]*?:= by)\b/gm,
            (_, header) => `${header} learning_guard ${JSON.stringify(snippet.allowedTactics.join(','))} in`)
        : payload.code;
      const source = prefix + checkedCode + (checkedCode.endsWith('\n') ? '' : '\n');
      // Ask Lean itself for transitive axiom dependencies, including dependencies
      // inherited from earlier unfinished lemmas. No source-text heuristic can
      // distinguish a complete proof from one that uses an admitted theorem.
      const names = [...new Set(payload.proofNames || [])].filter(name => /^[A-Za-z_][A-Za-z0-9_'.]*$/.test(name));
      const audit = names.map(name => `#print axioms ${name}\n`).join('');
      const document = {source: source + audit + closeScopes(source), code: payload.code,
        offset: prefix.split('\n').length - 1, version: (previous?.version || 0) + 1};
      // The public reader has one active editor. Bound retained source strings.
      sessions.clear();
      sessions.set(token, document);
      const result = await compile(document);
      const diagnostics = [];
      const contextErrors = [];
      const proofs = [];
      document.unsolved = [];
      for (const line of result.output) {
        let item;
        try { item = JSON.parse(line); } catch { continue; }
        const row = (item.pos?.line || 1) - document.offset;
        if (row - 1 >= source.split('\n').length - 1 - document.offset) {
          const match = /^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)/s.exec(item.data || '');
          if (match) proofs.push({name: match[1], axioms: match[2]?.split(',').map(name => name.trim()).filter(Boolean) || []});
          continue;
        }
        if (row < 1) {
          if (item.severity === 'error') contextErrors.push(item.data);
          continue;
        }
        const unfinished = item.kind === 'Tactic.unsolvedGoals' || item.kind === 'hasSorry'
          || /declaration uses [`']sorry[`']/.test(item.data || '');
        if (item.kind === 'Tactic.unsolvedGoals') document.unsolved.push({line: row - 1,
          text: item.data.replace(/^unsolved goals\s*\n/, '')});
        diagnostics.push({line: row, column: (item.pos?.column || 0) + 1,
          severity: item.severity === 'error' ? 1 : item.severity === 'warning' ? 2 : 3,
          kind: unfinished ? 'unfinished' : 'diagnostic', message: item.data, isSilent: item.isSilent});
      }
      return {session: token, version: document.version, diagnostics, contextErrors, proofs,
        ...await goals(document, payload.position || {line: 0, character: 0}, payload.proofRange)};
    }
    const document = sessions.get(payload.session);
    if (!document || document.version !== payload.version) throw new Error('The code changed. Run this example again.');
    if (path === '/api/lean/goal') return goals(document, payload.position, payload.proofRange);
    throw new Error('This browser editor does not yet provide Lean completion.');
  }
  return {call(path, payload) {
    const task = queue.catch(() => {}).then(() => execute(path, payload));
    queue = task;
    return task;
  }};
}
