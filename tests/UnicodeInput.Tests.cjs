const assert = require('node:assert/strict');
const fs = require('node:fs');
const http = require('node:http');
const path = require('node:path');
let playwright;
try { playwright = require('playwright'); }
catch { playwright = require(path.join(process.env.USERPROFILE, '.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright')); }

(async () => {
  const root = path.resolve('assets/web');
  const server = http.createServer((request, response) => {
    if (request.url === '/') {
      response.writeHead(200, {'Content-Type': 'text/html; charset=utf-8'}).end(`
        <textarea id="input"></textarea><button id="other">Other</button>
        <script type="module">
        import {attachUnicodeInput} from '/unicode-input.js';
        const input = document.querySelector('textarea');
        window.changes = 0;
        window.engine = attachUnicodeInput(input, () => ++window.changes);
        input.addEventListener('keydown', event => {
          if (event.key === 'Tab' && engine.hasPending()) {event.preventDefault(); engine.flush();}
        });
        window.reset = (value = '') => {input.value = value; engine.reset(); input.focus(); input.setSelectionRange(value.length, value.length);};
        </script>`);
      return;
    }
    const file = path.resolve(root, '.' + decodeURIComponent(request.url));
    if (!file.startsWith(root + path.sep) || !fs.existsSync(file)) { response.writeHead(404).end(); return; }
    response.writeHead(200, {'Content-Type': 'text/javascript; charset=utf-8'});
    fs.createReadStream(file).pipe(response);
  });
  await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
  const browser = await playwright.chromium.launch({channel: 'chrome', headless: true});
  try {
    const page = await browser.newPage();
    const errors = [];
    page.on('pageerror', error => errors.push(error.message));
    await page.goto(`http://127.0.0.1:${server.address().port}/`);
    await page.waitForFunction(() => !!window.engine);
    const input = page.locator('textarea');
    async function type(text, expected) {
      await page.evaluate(() => reset());
      await input.pressSequentially(text);
      assert.equal(await input.inputValue(), expected, text);
    }
    await type('\\forall', '∀');
    await type('\\exists', '∃');
    await type('\\alpha', 'α');
    await type('\\equiv', '≃');
    await type('\\== ', '≡ ');
    await type('x \\in S', 'x ∈ S');
    await type('x \\notin S', 'x ∉ S');
    await type('\\N ', 'ℕ ');
    await type('S\\^c ', 'Sᶜ ');
    await type('\\aleph0', 'ℵ₀');
    await type('\\in', '\\in');
    await input.press('Tab');
    assert.equal(await input.inputValue(), '∈');
    await type('\\l', '\\l');
    await input.press('Tab');
    assert.equal(await input.inputValue(), '←');
    await type('\\[[ ', '⟦ ');
    await type('\\[[]]', '⟦⟧');
    assert.equal(await input.evaluate(node => node.selectionStart), 1);
    await input.pressSequentially('x');
    assert.equal(await input.inputValue(), '⟦x⟧');
    await type('\\<>', '⟨⟩');
    assert.equal(await input.evaluate(node => node.selectionStart), 1);
    console.log('PASS: eager input, ambiguous prefixes, Space, Tab, Greek letters, superscripts, and paired cursors');

    await type('\\in', '\\in');
    await page.getByRole('button', {name: 'Other'}).click();
    assert.equal(await input.inputValue(), '∈');
    await page.evaluate(() => reset('prefix '));
    await input.pressSequentially('\\alpha');
    await input.press('Control+z');
    assert((await input.inputValue()).startsWith('prefix '), 'Undo must preserve the surrounding proof');
    await page.evaluate(() => reset());
    await input.pressSequentially('\\foral');
    await input.press('Backspace');
    await input.pressSequentially('ll');
    assert.equal(await input.inputValue(), '∀');
    await page.evaluate(() => reset());
    await input.fill('have h : \\forall x, P x := by\n  sorry');
    assert.equal(await input.inputValue(), 'have h : \\forall x, P x := by\n  sorry', 'Pasting code is not a sequence of abbreviation keystrokes');
    await page.evaluate(() => {
      reset(); const input = document.querySelector('textarea');
      input.dispatchEvent(new CompositionEvent('compositionstart'));
      input.value = '한글'; input.dispatchEvent(new InputEvent('input', {isComposing: true}));
      input.dispatchEvent(new CompositionEvent('compositionend'));
    });
    assert.equal(await input.inputValue(), '한글');
    await page.evaluate(() => reset('existing \\in'));
    await input.pressSequentially(' ');
    assert.equal(await input.inputValue(), 'existing \\in ', 'Restored drafts must not gain an active abbreviation');
    assert.deepEqual(errors, []);
    console.log('PASS: blur, undo, editing an abbreviation, pasted proofs, Korean IME, and restored drafts');
  } finally {
    await browser.close(); server.closeAllConnections(); await new Promise(resolve => server.close(resolve));
  }
})().catch(error => {console.error(error); process.exitCode = 1;});
