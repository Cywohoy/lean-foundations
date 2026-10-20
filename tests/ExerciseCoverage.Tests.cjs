// Exercise the published reader using static files only, with no Lean HTTP API.
const assert = require('node:assert/strict');
const fs = require('node:fs');
const http = require('node:http');
const path = require('node:path');
let playwright;
try { playwright = require('playwright'); }
catch { playwright = require(path.join(process.env.USERPROFILE, '.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright')); }
const site = path.resolve('_out/pages');
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
    const exercises = Object.entries(manifest).filter(([, item]) => item.exercise);
    assert(exercises.length > 50);
    assert.equal(new Set(exercises.map(([key]) => key)).size, exercises.length);
    const grouped = new Map();
    for (const [key, item] of exercises) {
      const selected = example(code => code === item.code);
      const list = grouped.get(selected.url) || [];
      list.push({key, item}); grouped.set(selected.url, list);
    }
    let visible = 0;
    for (const [url, entries] of grouped) {
      await page.goto(new URL(url, base).href);
      for (const {key} of entries) {
        const wrapper = page.locator(`[data-snippet="${key}"]`);
        assert.equal(await wrapper.getAttribute('data-exercise-unit'), 'exercises');
        assert.equal(await wrapper.locator('..').getByRole('button', {name:'풀기',exact:true}).count(), 1);
        visible++;
      }
    }
    assert.equal(visible,exercises.length);
    assert.equal(grouped.size,4);
    console.log(`PASS: all ${visible} exercise blocks expose the problem workspace on ${grouped.size} pages`);

    const result = await page.evaluate(async ({base, exercises}) => {
      const {createBrowserBackend} = await import(new URL('assets/web/wasm-reader.js', base));
      const {exerciseModel} = await import(new URL('assets/web/exercise-model.js', base));
      const backend = createBrowserBackend(base);
      const results = [];
      for (const [snippet, item] of exercises) {
        const model = exerciseModel(item.code);
        const line = item.code.slice(0, model.start(model.bodies,0)).split('\n').length-1;
        console.log('CHECK',snippet,model.parts[0].name);
        const checked = await backend.call('/api/lean/check', {snippet,code:item.code,
          proofNames:model.parts.map(part=>part.name), position:{line,character:2}});
        results.push({snippet,parts:model.parts.length,
          errors:checked.diagnostics.filter(item=>item.severity===1 && item.kind!=='unfinished'),
          contextErrors:checked.contextErrors,proofs:checked.proofs,goal:checked.goal});
      }
      return results;
    }, {base,exercises});
    fs.writeFileSync('tmp/all-exercise-wasm-results.json',JSON.stringify(result,null,2));
    for (const checked of result) {
      assert.deepEqual(checked.errors,[],JSON.stringify(checked));
      assert.deepEqual(checked.contextErrors,[],JSON.stringify(checked));
      assert(checked.goal?.length,JSON.stringify(checked));
      assert.equal(checked.proofs.length,checked.parts,JSON.stringify(checked));
      assert(checked.proofs.every(proof=>proof.axioms.includes('sorryAx')),JSON.stringify(checked));
    }
    const proofCount = result.reduce((n,item)=>n+item.parts,0);
    assert(proofCount > 90);
    assert.deepEqual(uploads,[]); assert.deepEqual(errors,[]);
    console.log(`PASS: all ${result.length} exercise contexts / ${proofCount} proofs compile in WASM, expose an initial goal, and report admitted dependencies`);
  } finally {
    await browser.close(); server.closeAllConnections();
    await new Promise(resolve=>server.close(resolve));
  }
}
main().catch(error=>{console.error(error);process.exitCode=1;});

