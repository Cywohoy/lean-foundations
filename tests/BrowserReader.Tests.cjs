// Exercise the published reader using static files only, with no Lean HTTP API.
const assert = require('node:assert/strict');
const fs = require('node:fs');
const http = require('node:http');
const path = require('node:path');
let playwright;
try { playwright = require('playwright'); }
catch { playwright = require(path.join(process.env.USERPROFILE, '.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright')); }
const site = path.resolve(process.env.BOOK_SITE || '_out/pages');
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
    if (!fs.existsSync(file)) { console.error('MISSING FILE:',pathname,file); response.writeHead(404).end(); return; }
    const mime = {'.html': 'text/html', '.js': 'text/javascript', '.css': 'text/css', '.json': 'application/json', '.wasm': 'application/wasm'};
    response.writeHead(200, {'Content-Type': mime[path.extname(file)] || 'application/octet-stream', 'Content-Length': fs.statSync(file).size});
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
    page.on('console', message => { if (message.type() === 'error' || process.env.TRACE_WASM) console.error('BROWSER:', message.text()); });
    page.on('requestfailed', request => console.error('REQUEST:', request.url(), request.failure()?.errorText));
    page.on('response', response => { if (response.status() >= 400) console.error('HTTP',response.status(),response.url()); });
    page.on('request', request => { if (request.method() !== 'GET' || request.postData()) uploads.push(request.url()); });
    async function open(selected) {
      await page.goto(new URL(selected.url, base).href);
      const wrapper = page.locator(`[data-snippet="${selected.key}"]`);
      await wrapper.hover();
      await wrapper.locator('..').getByRole('button', {name: '풀기', exact: true}).click();
      await wrapper.locator('textarea').waitFor();
      return wrapper;
    }
    async function status(wrapper, expected) {
      try {
        const key = await wrapper.getAttribute('data-snippet');
        await page.waitForFunction(({key, expected}) => {
          const text = document.querySelector(`[data-snippet="${key}"] .book-run-status`)?.textContent;
          return text?.includes(expected) || text === '실행 실패' || /^오류 \d+개$/.test(text || '');
        }, {key, expected}, {timeout: 120000});
        assert((await wrapper.locator('.book-run-status').innerText()).includes(expected));
      }
      catch (error) { console.error(await wrapper.locator('.book-live-editor').innerText()); throw error; }
    }
    const selected = example(code => code.startsWith('example {A : Type _} {S T : Set A}') && code.includes('funext x'));
    await page.goto(new URL(selected.url, base).href);
    let wrapper = page.locator(`[data-snippet="${selected.key}"]`);
    assert.equal(await page.getByRole('button', {name: '편집', exact: true}).count(), 0);
    await wrapper.getByRole('button', {name: '단계 보기', exact: true}).click();
    assert(await wrapper.locator('.book-step-state').isVisible());
    assert(await wrapper.locator('.book-example-body > .hl.lean.block').evaluate(code =>
      parseFloat(getComputedStyle(code).paddingTop) <= 12
    ), 'proof controls must overlay the code block without reserving a row above it');
    console.log('PASS: visible proof steps and no standalone edit controls');

    const exercise = example(code => code.startsWith('theorem exercise_add_three_preserves_lt'));
    // An earlier edition saved by source position. Keep that proof after moving the problem.
    await page.evaluate(({key, code}) => localStorage.setItem('lean-algebra.code.' + key, code), {
      key: exercise.data.legacyKeys.at(-1),
      code: exercise.data.code.replace('sorry', '-- retained from the previous edition\n  sorry')
    });
    wrapper = await open(exercise);
    await status(wrapper, '증명 중');
    assert(await wrapper.locator('dialog').isVisible());
    assert.equal(await wrapper.getByRole('button', {name: '단계 보기', exact: true}).count(), 0);
    assert((await wrapper.locator('.book-exercise-heading').innerText()).includes('문제 2'));
    assert((await wrapper.locator('.book-live-editor > .book-exercise-declaration').innerText()).includes('a + 3 < b + 3'));
    assert.equal(await wrapper.locator('textarea').inputValue(), '-- retained from the previous edition\nsorry');
    assert(await wrapper.locator('..').locator('.book-solve-button').evaluate(button => {
      const rect = button.getBoundingClientRect(); return rect.height >= 44 && rect.width <= 120;
    }));
    assert(await wrapper.locator('.book-editor-controls').evaluate(controls => controls.getBoundingClientRect().height < 90));
    for (const malformed of ['nonsense', 'nonsense\nnonsense']) {
      await wrapper.locator('textarea').fill(malformed);
      await status(wrapper, '오류');
      assert((await wrapper.locator('.book-diagnostics').innerText()).includes('unknown tactic'));
      await wrapper.locator('textarea').evaluate(input => {
        input.setSelectionRange(input.value.length, input.value.length);
        input.dispatchEvent(new MouseEvent('click', {bubbles: true}));
      });
      await page.waitForFunction(() => document.querySelector('.book-live-goal')?.textContent.includes('⊢ a + 3 < b + 3'));
      if (malformed.includes('\n')) assert((await wrapper.locator('.book-live-output > .book-panel-heading').innerText()).includes('남은 목표'));
    }
    await wrapper.locator('textarea').fill('');
    await page.waitForFunction(() => document.querySelector('.book-live-goal')?.textContent.includes('⊢ a + 3 < b + 3'), null, {timeout: 120000});
    const branchProof = 'expand; ext\nexists fun x => ⟨x+2, by arith⟩\nconstructor\n· intro x y hxy';
    await wrapper.locator('textarea').fill(branchProof);
    await wrapper.locator('textarea').press('Enter');
    assert.equal(await wrapper.locator('textarea').inputValue(), branchProof + '\n  ');
    await wrapper.locator('textarea').pressSequentially('have h : x = y := by');
    await wrapper.locator('textarea').press('Enter');
    assert((await wrapper.locator('textarea').inputValue()).endsWith(':= by\n    '));
    await wrapper.locator('textarea').fill('· have h : True := by -- a nested proof');
    await wrapper.locator('textarea').press('Enter');
    assert((await wrapper.locator('textarea').inputValue()).endsWith('\n    '));
    await wrapper.locator('textarea').fill('apply Nat.add_lt_add_right (k := 3)\nexact h');
    await status(wrapper, '풀이 완료');
    // Full-source mode preserves the proof, and changed statements are not marked solved.
    await wrapper.getByRole('button', {name: '전체 코드', exact: true}).click();
    assert((await wrapper.locator('textarea').inputValue()).startsWith('theorem exercise_'));
    const canonical = await wrapper.locator('textarea').inputValue();
    await wrapper.locator('textarea').fill('theorem exercise_add_three_preserves_lt (P Q : Prop) :\n    (P → P) ∧ (Q → Q) := by\n  constructor\n  · intro hP');
    await wrapper.locator('textarea').press('Enter');
    assert((await wrapper.locator('textarea').inputValue()).endsWith('\n    '));
    await wrapper.locator('textarea').pressSequentially('exact hP');
    await wrapper.locator('textarea').fill((await wrapper.locator('textarea').inputValue()) + '\n  · intro hQ');
    await wrapper.locator('textarea').press('Enter');
    await wrapper.locator('textarea').pressSequentially('exact hQ');
    await wrapper.locator('textarea').press('Control+Enter');
    await status(wrapper, '코드 검사 통과');
    await wrapper.locator('textarea').fill('theorem exercise_add_three_preserves_lt : ');
    await wrapper.locator('textarea').pressSequentially('\\forall');
    const typedDeclaration = await wrapper.locator('textarea').inputValue();
    assert(typedDeclaration.endsWith('∀'), typedDeclaration);
    await wrapper.locator('textarea').fill(typedDeclaration + ' n : Nat, n = n := by\n  intro n\n  rfl');
    await wrapper.locator('textarea').press('Control+Enter');
    await status(wrapper, '코드 검사 통과');
    assert((await page.evaluate(key => localStorage.getItem('lean-algebra.code.' + key), exercise.data.storageKey)).includes('∀ n : Nat'));
    await wrapper.locator('textarea').fill('theorem exercise_add_three_preserves_lt : True := by\n  trivial');
    await status(wrapper, '코드 검사 통과');
    await wrapper.locator('textarea').fill('axiom unproved : True\ntheorem exercise_add_three_preserves_lt : True := by\n  exact unproved');
    await status(wrapper, '미완성 · 허용되지 않은 공리');
    assert(!await wrapper.locator('.book-run-status').evaluate(node => node.classList.contains('book-success')));
    await wrapper.locator('textarea').fill(canonical);
    await wrapper.getByRole('button', {name: '증명만 편집', exact: true}).click();
    await status(wrapper, '풀이 완료');
    assert(await wrapper.locator('.book-reader-panel').evaluate(panel => panel.getBoundingClientRect().width > 1000));
    const downloadEvent = page.waitForEvent('download');
    await wrapper.getByRole('button', {name: '풀이 내려받기', exact: true}).click();
    const download = await downloadEvent;
    assert(download.suggestedFilename().endsWith('.lean'));
    await download.saveAs('tmp/browser-exercise-download.lean');
    const downloaded = fs.readFileSync('tmp/browser-exercise-download.lean', 'utf8');
    assert(downloaded.includes('import Ample.') && downloaded.includes('exact h'));
    await page.keyboard.press('Escape');
    assert.equal(await wrapper.locator('dialog').isVisible(), false);
    await wrapper.locator('.book-example-body > .hl.lean.block').click({position: {x: 8, y: 8}});
    assert((await wrapper.locator('textarea').inputValue()).includes('exact h'));
    await status(wrapper, '풀이 완료');
    await page.screenshot({path: 'tmp/exercise-workspace-desktop.png'});
    await page.setViewportSize({width: 390, height: 844});
    const layout = await wrapper.locator('dialog').evaluate(dialog => ({
      width: dialog.getBoundingClientRect().width, overflow: dialog.scrollWidth > dialog.clientWidth,
      code: dialog.querySelector('textarea').getBoundingClientRect().bottom,
      goals: dialog.querySelector('.book-live-output').getBoundingClientRect().top,
    }));
    assert(layout.width <= 390 && !layout.overflow && layout.goals >= layout.code, JSON.stringify(layout));
    await page.screenshot({path: 'tmp/exercise-workspace-mobile.png'});
    await page.setViewportSize({width: 1360, height: 1000});
    await page.keyboard.press('Escape');
    await page.reload();
    wrapper = page.locator(`[data-snippet="${exercise.key}"]`);
    await wrapper.locator('..').getByRole('button', {name: '풀기', exact: true}).click();
    assert((await wrapper.locator('textarea').inputValue()).includes('exact h'));
    await status(wrapper, '풀이 완료');
    await page.keyboard.press('Escape');
    console.log('PASS: proof-only exercise workspace, draft, download, mode switch, and responsive layout');

    const chain = example(code => code.startsWith('theorem exercise_shift_lt '));
    wrapper = await open(chain);
    await status(wrapper, '증명 중');
    await wrapper.locator('textarea').fill('apply Nat.add_lt_add_right (k := c)\nexact hab');
    await status(wrapper, '증명 완료 (1/2 완료)');
    await wrapper.getByRole('button', {name: '(2)', exact: true}).click();
    await wrapper.locator('textarea').fill('apply exercise_shift_lt\napply exercise_shift_lt\nexact hab');
    await status(wrapper, '풀이 완료');
    await wrapper.getByRole('button', {name: '(1)', exact: true}).click();
    assert((await wrapper.locator('textarea').inputValue()).includes('(k := c)'));
    await status(wrapper, '풀이 완료');
    await wrapper.locator('textarea').fill('exact True.intro');
    await status(wrapper, '오류 1개');
    await wrapper.locator('.book-diagnostics .book-error').first().click();
    assert.equal(await wrapper.locator('textarea').evaluate(input => input.selectionStart), 0);
    assert((await wrapper.locator('.book-diagnostics').innerText()).includes('1:1'));
    await wrapper.locator('textarea').fill('apply Nat.add_lt_add_right (k := c)\nexact True.intro');
    await status(wrapper, '오류 1개');
    await wrapper.locator('.book-diagnostics .book-error').first().click();
    assert.equal(await wrapper.locator('textarea').evaluate(input => input.selectionStart),
      (await wrapper.locator('textarea').inputValue()).indexOf('\n') + 1);
    assert((await wrapper.locator('.book-diagnostics').innerText()).includes('2:1'));
    await wrapper.locator('textarea').fill('sorry');
    await status(wrapper, '증명 중');
    await wrapper.getByRole('button', {name: '(2)', exact: true}).click();
    await status(wrapper, '증명 중');
    assert((await wrapper.locator('.book-diagnostics').innerText()).includes('미완성 정리'));
    assert(!await wrapper.locator('.book-run-status').evaluate(node => node.classList.contains('book-success')));
    await wrapper.getByRole('button', {name: '(1)', exact: true}).click();
    await wrapper.locator('textarea').fill('apply Nat.add_lt_add_right (k := c)\nexact hab');
    await status(wrapper, '풀이 완료');
    await page.keyboard.press('Escape');
    console.log('PASS: dependent subproblems, transitive admission checks, and diagnostic cursor mapping');

    const repeated = example(code => code.startsWith('theorem exercise_from_two_countably_infinite '));
    wrapper = await open(repeated);
    await status(wrapper, '증명 중');
    // A pthread mailbox callback used to shut the runtime down between edits.
    // Leave the event loop idle, then exercise each way of checking new code.
    await page.waitForTimeout(2500);
    await wrapper.locator('textarea').fill('expand');
    await wrapper.locator('textarea').press('Control+Enter');
    await page.waitForFunction(key => document.querySelector(`[data-snippet="${key}"] .book-live-goal`)?.textContent.includes('⊢ cardinal Nat = cardinal'), repeated.key);
    await page.waitForTimeout(2500);
    await wrapper.locator('textarea').fill('unknown_tactic');
    await wrapper.getByRole('button', {name:'검사', exact:true}).click();
    await status(wrapper, '오류');
    assert((await wrapper.locator('.book-diagnostics').innerText()).includes('unknown tactic'));
    await page.waitForTimeout(2500);
    await wrapper.locator('textarea').fill('expand');
    await status(wrapper, '증명 중');
    assert((await wrapper.locator('.book-live-goal').innerText()).includes('⊢ cardinal Nat = cardinal'));
    await page.keyboard.press('Escape');
    console.log('PASS: automatic checking, check button, and Ctrl+Enter survive idle periods without reloading');

    const progression = example(code => code.includes('theorem exercise_oneModThree_bijective'));
    wrapper = await open(progression);
    await status(wrapper, '증명 중');
    const failingArithmetic = `constructor
· intro x y hxy
  indisc at hxy
  arith
· intro y
  exists (y.val - 1) / 3
  ext
  arith`;
    for (let attempt = 0; attempt < 3; attempt++) {
      const proof = attempt === 1
        ? failingArithmetic.replace(/  arith$/, '  suffices (3 ∣ (y.val - 1)) by arith\n  sorry')
        : failingArithmetic;
      await wrapper.locator('textarea').fill(proof + ` -- attempt ${attempt}`);
      await wrapper.locator('textarea').press('Control+Enter');
      await status(wrapper, '오류');
      const panel = await wrapper.locator('.book-live-editor').innerText();
      assert(!panel.includes('Lean 실행이 중단되었습니다'), panel);
      assert(panel.includes('Arithmetic could not close the goal'), panel);
      if (attempt === 0) {
        await wrapper.locator('textarea').press('Home');
        await wrapper.locator('textarea').press('ArrowRight');
        await wrapper.locator('textarea').press('ArrowRight');
        await page.waitForFunction(key => {
          const text = document.querySelector(`[data-snippet="${key}"] .book-live-goal`)?.textContent;
          return text?.includes('y : Elem') && text.includes('⊢');
        }, progression.key, {timeout: 15000});
      }
    }
    await wrapper.locator('textarea').fill(`constructor
· intro x y hxy
  indisc at hxy
  arith
· intro y
  rcases y.property with ⟨k, hk⟩
  exists k
  ext
  exact hk.symm`);
    await wrapper.locator('textarea').press('Control+Enter');
    await status(wrapper, '증명 완료 (1/3 완료)');
    await page.keyboard.press('Escape');
    console.log('PASS: failed arithmetic searches report diagnostics and allow a corrected proof without reloading');

    const cantor = example(code => code.startsWith('theorem cantor_not_surjective '));
    const concrete = example(code => code.startsWith('theorem cardinal_fin '));
    // Worked examples have static proof states, not editable browser contexts.
    // Recheck their proof bodies inside the later exercise's supported context.
    const runtimeContext = example(code => code.includes('theorem exercise_singleton_not_surjective'));
    await page.goto(new URL(runtimeContext.url, base).href);
    const inverse = `example {A B : Type} (f : A → B) (hf : Bijective f) (x : A) (y : B) :
    inverseMap f hf (f x) = x ∧ f (inverseMap f hf y) = y := by
  have hI : Injective f := hf.inj
  have hS : Surjective f := hf.surj
  constructor
  · exact inverseMap_left f hf x
  · exact inverseMap_right f hf y`;
    const checks = await page.evaluate(async ({base, tests}) => {
      const {createBrowserBackend} = await import(new URL('assets/web/wasm-reader.js', base));
      const backend = createBrowserBackend(base);
      const results = [];
      for (const test of tests) results.push(await backend.call('/api/lean/check', test));
      return results;
    }, {base, tests: [
      {snippet: runtimeContext.key, code: cantor.data.code.replace('theorem cantor_not_surjective', 'example')},
      {snippet: runtimeContext.key, code: concrete.data.code.replace('theorem cardinal_fin', 'example'),
        position: {line: concrete.data.code.split('\n').findIndex(line => line.includes('rfl')), character: 2}},
      {snippet: runtimeContext.key, code: inverse},
      {snippet: progression.key, code: `example (x y : Int) :
    (x + y) * (x - y) = x * x - y * y := by arith
example (n : Int) (h : 0 < n) : 3 / n ≤ 3 := by arith
example (n m : Nat) (h : n * m = 3) (hn : n ≠ 0) : m ≤ 3 := by arith
example (k : Int) : ¬ (2 ∣ 2 * k + 1) := by arith`},
    ]});
    for (const check of checks) {
      assert.deepEqual(check.contextErrors, []);
      assert(!check.diagnostics.some(item => item.severity === 1), JSON.stringify(check));
    }
    const state = checks[1].goal.join('\n');
    assert(state.includes('n : Nat') && !/\b[A-C] : Type|\bm : Nat/.test(state), state);
    assert.deepEqual(uploads, [], 'Proof text must stay in the browser');
    assert.deepEqual(errors, []);
    console.log('PASS: diagonal argument, cardinality context, concise accessors, inverse identities, and browser-only compilation');

  } finally {
    await browser.close(); server.closeAllConnections();
    await new Promise(resolve => server.close(resolve));
  }
}
main().catch(error => {console.error(error); process.exitCode = 1;});
