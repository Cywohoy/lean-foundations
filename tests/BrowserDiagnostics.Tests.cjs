/* Uses an existing preview; this test never starts or stops a server. */
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
let playwright;
try { playwright = require('playwright'); }
catch { playwright = require(path.join(process.env.USERPROFILE, '.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright')); }
const base = process.env.BOOK_URL || 'http://127.0.0.1:8000/foundations/';
const manifest = JSON.parse(fs.readFileSync('_out/pages/foundations/playground.json', 'utf8'));
const [key] = Object.entries(manifest).find(([, value]) => value.exercise && value.code.includes('exercise_parityClass_three_one'));

(async () => {
  const browser = await playwright.chromium.launch({channel:'chrome', headless:true});
  try {
    const page = await browser.newPage({viewport:{width:1360, height:1000}, permissions:['clipboard-read','clipboard-write']});
    await page.goto(new URL('numbers-relations/', base).href);
    const wrapper = page.locator(`[data-snippet="${key}"]`);
    await wrapper.locator('..').getByRole('button', {name:'풀기', exact:true}).click();
    const input = wrapper.locator('textarea');
    const status = wrapper.locator('.book-run-status');
    async function finished(text) {
      await page.waitForFunction(({key, text}) => {
        const status = document.querySelector(`[data-snippet="${key}"] .book-run-status`)?.textContent;
        return status?.includes(text) || status === '실행 실패';
      }, {key, text}, {timeout:180000});
      assert((await status.innerText()).includes(text), await wrapper.locator('.book-live-editor').innerText());
    }
    // Wait for the checked catalog rather than querying during initial setup.
    await finished('증명 중');
    const theoremSearch = wrapper.getByRole('searchbox', {name:'정리 검색'});
    await theoremSearch.fill('parityClass_zero_ne_one');
    const theorem = wrapper.locator('.book-theorem');
    assert.equal(await theorem.count(), 1);
    assert((await theorem.innerText()).includes('parityClass 0 ≠ parityClass 1'));
    await theorem.getByRole('button').click();
    assert.equal(await page.evaluate(() => navigator.clipboard.readText()), 'parityClass_zero_ne_one');
    await theoremSearch.fill('quotientLift_unique');
    assert.equal(await theorem.count(), 0, 'Later theorems must not be suggested');
    await theoremSearch.fill('');
    console.log('PASS: browser context is ready');
    await input.fill('have h := parityClass_zero_ne_one_misspelled\nsorry');
    await finished('오류');
    assert((await wrapper.locator('.book-diagnostics').innerText()).includes('Unknown identifier `parityClass_zero_ne_one_misspelled`'));
    console.log('PASS: missing theorem in have is shown');
    await wrapper.locator('.book-diagnostics .book-error').first().click();
    assert((await input.evaluate(node => node.value.slice(0,node.selectionStart))).includes('have h :='));
    await input.fill('rw [parityClass_zero_ne_one_misspelled]');
    await finished('오류');
    assert((await wrapper.locator('.book-diagnostics').innerText()).includes('Unknown identifier `parityClass_zero_ne_one_misspelled`'));
    console.log('PASS: a missing rewrite theorem retains its diagnostic');
    await input.fill('have h : 0 = 1 := by\n  rfl\nsorry');
    await finished('오류');
    await page.waitForFunction(key => document.querySelector(`[data-snippet="${key}"] .book-diagnostics`)?.textContent.includes('failed'),key);
    await input.fill('have h := parityClass_zero_ne_one\next\nexists 1');
    await finished('증명 완료');
    assert(!await wrapper.locator('.book-diagnostics .book-error').count());
    await wrapper.getByRole('button', {name:'(2)', exact:true}).click();
    await theoremSearch.fill('exercise_parityClass_three_one');
    assert.equal(await theorem.count(), 1, 'The preceding subproblem is a usable named result');
    await theoremSearch.fill('');
    await input.fill('intro h\napply parityClass_zero_ne_one\nrw [← h]\nexact exercise_parityClass_three_one');
    await finished('풀이 완료');
    for (const selector of ['.book-code-input','.book-exercise-declaration','.book-live-goal']) {
      for (const node of await wrapper.locator(selector).all()) {
        assert.equal(await node.evaluate(node => getComputedStyle(node).fontVariantLigatures),'none');
      }
    }
    assert.equal(await page.locator('main .hl.lean.block').first().evaluate(node => getComputedStyle(node).fontVariantLigatures),'none');
    assert(!await status.evaluate(node => node.classList.contains('book-error')));
    await page.setViewportSize({width:390,height:844});
    const panel = wrapper.locator('.book-theorems');
    assert(await panel.isVisible());
    assert(!await wrapper.locator('dialog').evaluate(node => node.scrollWidth > node.clientWidth));
    console.log('PASS: have diagnostics, real theorem search and copy, chronology, prior subproblem, both parity proofs, ligatures, and mobile layout');
  } finally { await browser.close(); }
})().catch(error => { console.error(error); process.exitCode = 1; });
