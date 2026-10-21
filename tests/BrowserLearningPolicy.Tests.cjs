// Verify curriculum-based tactic restrictions using the real browser Lean runtime.
const assert = require('node:assert/strict');
const fs = require('node:fs');
const http = require('node:http');
const path = require('node:path');
let playwright;
try { playwright = require('playwright'); }
catch { playwright = require(path.join(process.env.USERPROFILE, '.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright')); }
const site = path.resolve('_out/pages/foundations');
const localManifest = JSON.parse(fs.readFileSync(path.join(site, 'playground.json'), 'utf8'));
let manifest = localManifest;
const uploads = [];
function walk(directory) {
  return fs.readdirSync(directory, {withFileTypes: true}).flatMap(entry => {
    const file = path.join(directory, entry.name);
    return entry.isDirectory() ? walk(file) : file.endsWith('.html') ? [file] : [];
  });
}
const pages = walk(site);
function example(match) {
  const pair = Object.entries(manifest).find(([, value]) => match(value.code));
  assert(pair, 'The selected textbook example disappeared');
  const [key, data] = pair;
  const localKey = Object.entries(localManifest).find(([, value]) => value.code === data.code)?.[0] || key;
  const file = pages.find(file => fs.readFileSync(file, 'utf8').includes(`data-snippet="${localKey}"`));
  assert(file, key);
  return {key, data, url: path.relative(site, file).replaceAll('\\', '/').replace(/index\.html$/, '')};
}
async function main() {
  const server = http.createServer((request, response) => {
    const pathname = decodeURIComponent(new URL(request.url, 'http://localhost').pathname);
    if (request.method !== 'GET') uploads.push(pathname);
    if (pathname === '/favicon.ico') { response.writeHead(204).end(); return; }
    if (!pathname.startsWith('/lean-algebra/')) { response.writeHead(404).end(); return; }
    let file = path.resolve(site, pathname.slice('/lean-algebra/'.length));
    if (!file.startsWith(site + path.sep)) { response.writeHead(403).end(); return; }
    if (fs.existsSync(file) && fs.statSync(file).isDirectory()) file = path.join(file, 'index.html');
    if (!fs.existsSync(file)) { response.writeHead(404).end(); return; }
    const mime = {'.html': 'text/html', '.js': 'text/javascript', '.css': 'text/css', '.json': 'application/json', '.wasm': 'application/wasm'};
    response.writeHead(200, {'Cross-Origin-Opener-Policy':'same-origin','Cross-Origin-Embedder-Policy':'require-corp','Content-Type': mime[path.extname(file)] || 'application/octet-stream', 'Content-Length': fs.statSync(file).size});
    fs.createReadStream(file).pipe(response);
  });
  await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
  const base = process.env.BOOK_URL || `http://127.0.0.1:${server.address().port}/lean-algebra/`;
  if (process.env.BOOK_URL) manifest = await (await fetch(new URL('playground.json', base))).json();
  const browser = await playwright.chromium.launch({channel: 'chrome', headless: true});
  try {
    const page = await browser.newPage({viewport: {width: 1360, height: 1000}});
    if (process.env.TRACE_WASM) await page.addInitScript(() => {
      const NativeWorker = Worker;
      window.Worker = class extends NativeWorker {
        constructor(...args) {
          super(...args);
          this.addEventListener('message', ({data}) => {
            console.log('WORKER', JSON.stringify({type: data.type, success: data.success, data: data.data, error: data.error, elapsed: data.elapsed}));
          });
        }
      };
    });
    const errors = [];
    page.on('pageerror', error => { errors.push(error.message); console.error(error.message); });
    page.on('console', message => {
      if (message.type() === 'error' || process.env.TRACE_WASM || message.text().startsWith('CHECK '))
        console.error('BROWSER:', message.text());
    });
    page.on('requestfailed', request => console.error('REQUEST:', request.url(), request.failure()?.errorText));
    page.on('request', request => { if (request.method() !== 'GET' || request.postData()) uploads.push(request.url()); });
    await page.goto(new URL('proof/',base).href);
    const exercise=example(code=>code.startsWith('theorem exercise_add_three_preserves_lt'));
    const results=await page.evaluate(async ({base, exercise})=>{
      const {createBrowserBackend}=await import(new URL('assets/web/wasm-reader.js',base));
      const backend=createBrowserBackend(base); const results=[];
      for (const body of ['nonsense','nonsense\nnonsense','trivial','exact (by trivial)','apply Nat.add_lt_add_right (k := 3)\nexact h']) {
        const code=exercise.data.code.replace('sorry',body.replaceAll('\n','\n  '));
        const endLine=code.trimEnd().split('\n').length-1;
        const checked=await backend.call('/api/lean/check',{snippet:exercise.key, code, proofNames:['exercise_add_three_preserves_lt'], proofRange:{startLine:0,endLine},position:{line:endLine,character:100}});
        results.push({body,...checked});
      }
      return results;
    }, {base,exercise});
    for (const result of results.slice(0,4)) {
      const errors=result.diagnostics.filter(item=>item.severity===1 && item.kind!=='unfinished');
      assert.equal(errors.length,1,JSON.stringify(result));
      assert(result.goal?.join('\n').includes('⊢ a + 3 < b + 3'),JSON.stringify(result));
      if (result.body.includes('nonsense')) assert(errors[0].message.includes('unknown tactic'));
      else assert(errors[0].message.includes("Tactic 'trivial' has not been introduced"));
      assert(result.proofs[0].axioms.includes('sorryAx'));
    }
    assert.deepEqual(results.at(-1).diagnostics,[]);
    assert.deepEqual(results.at(-1).proofs[0].axioms,[]);
    const later=example(code=>code.startsWith('theorem exercise_subset_chain'));
    const arithmetic=example(code=>code.startsWith('theorem exercise_equal_values_equivalence'));
    const taught=await page.evaluate(async ({base,later,arithmetic})=>{
      const {createBrowserBackend}=await import(new URL('assets/web/wasm-reader.js',base));
      const backend=createBrowserBackend(base);
      const results=[];
      for (const [snippet,code] of [[later.key,'example : True := by trivial'],
         [arithmetic.key,'example (n : Int) : n + 0 = n := by arith']]) {
        results.push(await backend.call('/api/lean/check',{snippet,code}));
      }
      return results;
    },{base,later,arithmetic});
    for(const result of taught) {
      assert.deepEqual(result.contextErrors,[]);
      assert(!result.diagnostics.some(item=>item.severity===1),JSON.stringify(result));
    }
    assert.deepEqual(uploads,[]);
    assert.deepEqual(errors,[]);
    console.log('PASS: unintroduced and nested tactics are blocked, goals survive errors, and taught tactics succeed');
  } finally {
    await browser.close(); server.closeAllConnections();
    await new Promise(resolve=>server.close(resolve));
  }
}
main().catch(error=>{console.error(error);process.exitCode=1;});

