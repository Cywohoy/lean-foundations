/* Check reader states from generated Lean output without starting a server. */
const assert = require('node:assert/strict');
const fs = require('node:fs/promises');
const path = require('node:path');
let playwright;
try { playwright = require('playwright'); }
catch { playwright = require(path.join(process.env.USERPROFILE,
  '.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright')); }
const root = path.resolve(__dirname, '..');

async function main() {
  const browser = await playwright.chromium.launch({headless: true,
    executablePath: process.env.CHROME_PATH || (process.platform === 'win32'
      ? 'C:/Program Files/Google/Chrome/Application/chrome.exe' : undefined)});
  try {
    const context = await browser.newContext({serviceWorkers: 'block'});
    // Serve generated markup inside the browser; suppress unrelated page scripts.
    await context.route('**/*', async route => {
      const chapter = new URL(route.request().url()).pathname.split('/')[1];
      if (!['proof', 'numbers-relations', 'sets-functions', 'sizes'].includes(chapter) ||
          route.request().resourceType() !== 'document') return route.abort();
      const html = await fs.readFile(path.join(root, '_out/html-multi', chapter, 'index.html'), 'utf8');
      await route.fulfill({contentType: 'text/html', body: html
        .replace(/<script\b[^>]*>[\s\S]*?<\/script>/gi, '')
        .replace(/<link\b[^>]*>/gi, '')
        .replace(/<meta\b[^>]*name="book-mode"[^>]*>/gi, '')});
    });
    const page = await context.newPage();
    const errors = [];
    page.on('pageerror', error => errors.push(error.message));
    async function chapter(name) {
      await page.goto(`https://reader.test/${name}/`);
      await page.addScriptTag({path: path.join(root, 'assets/web/reader.js')});
    }
    async function readSteps(proof) {
      await proof.getByRole('button', {name: '단계 보기', exact: true}).click();
      const steps = [];
      for (let i = 0; i < 80; i++) {
        steps.push({title: await proof.locator('.book-step-title').innerText(),
          state: await proof.locator('.book-step-state').innerText(),
          goals: await proof.locator('.book-step-state .goal').count()});
        const next = proof.getByRole('button', {name: '다음 →', exact: true});
        if (await next.isDisabled()) return steps;
        await next.click();
      }
      throw new Error('Unexpected step sequence');
    }

    await chapter('numbers-relations');
    const unique = page.locator('.book-example').filter({has: page.locator('#Ample___quotientLift_unique')});
    const steps = await readSteps(unique);
    assert.equal(steps.at(-1).title, 'rw [ha, hF a, hG a]');
    assert.equal(steps.at(-1).goals, 0, 'Final rw state includes automatic reflexivity');
    assert.equal(steps.at(-1).state, '남은 목표 없음');
    assert.match(steps.at(-2).state, /f a = f a/, 'The intermediate last-rule state stays available');
    assert(steps.some(step => /F ⟦a⟧ = G ⟦a⟧/.test(step.state)), 'Earlier rewrites stay available');
    // Clicking the tactic itself selects the final state, not the last rule.
    await unique.locator('.tactic > label').filter({hasText: /^rw \[ha,/}).click();
    assert.equal(await unique.locator('.book-step-state').innerText(), '남은 목표 없음');

    // A rewrite with remaining goals must still show them, not report completion.
    const unfinished = await page.locator('.book-example').evaluateAll(blocks => {
      for (const [index, block] of blocks.entries()) {
        for (const tactic of block.querySelectorAll('.tactic')) {
          const label = tactic.querySelector(':scope > label');
          const state = tactic.querySelector(':scope > .tactic-state');
          if (!label || !state?.querySelector('.goal') || !label.querySelector('.tactic')) continue;
          const copy = label.cloneNode(true);
          copy.querySelectorAll('.tactic-state, .tactic-toggle, .hover-container, .hover-info').forEach(el => el.remove());
          if (/^(rw|rewrite)\b/.test(copy.textContent.trim())) return index;
        }
      }
      return -1;
    });
    assert(unfinished >= 0, 'The generated chapter includes a nonfinal compound rewrite');
    const pending = await readSteps(page.locator('.book-example').nth(unfinished));
    assert(pending.some(step => /^(rw|rewrite)\b/.test(step.title) && step.goals > 0),
      'Compound rewrite states retain unresolved goals');

    await chapter('sets-functions');
    const trans = page.locator('.book-example').filter({has: page.locator('#Ample___subset_trans')});
    const nested = await readSteps(trans);
    const inner = nested.findIndex(step => step.title === 'exact hST x hx');
    assert(inner >= 0, 'Nested have proof remains a separate step');
    assert.equal(nested[inner].state, '보조 증명 완료');
    assert(nested.slice(inner + 1).some(step => /^have\b/.test(step.title) && step.goals > 0),
      'The outer proof state resumes after have');

    // Inspect the last reader step of every checked, hole-free code block.
    // This covers other transformations as well as compound proof commands.
    let checked = 0;
    const partial = [];
    const commands = new Set();
    for (const name of ['proof', 'sets-functions', 'numbers-relations', 'sizes']) {
      await chapter(name);
      const result = await page.evaluate(() => {
        const plain = node => {
          const copy = node.cloneNode(true);
          copy.querySelectorAll('.tactic-state, .tactic-toggle, .hover-container, .hover-info').forEach(el => el.remove());
          return copy.textContent.trim();
        };
        const checked = [];
        for (const block of document.querySelectorAll('.book-example')) {
          const source = block.querySelector('code.hl.lean.block');
          const text = source && plain(source);
          const open = [...block.querySelectorAll('button')].find(b => b.textContent === '단계 보기');
          if (!text || /\bsorry\b/.test(text) || !open) continue;
          open.click();
          const next = [...block.querySelectorAll('button')].find(b => b.textContent === '다음 →');
          const commands = [];
          for (let i = 0; i < 200; i++) {
            commands.push(block.querySelector('.book-step-title').textContent.split(/[\s\[]/)[0]);
            if (next.disabled) break;
            next.click();
            if (i === 199) throw new Error('Unexpected step sequence');
          }
          checked.push({text, commands, goals: block.querySelectorAll('.book-step-state .goal').length});
          open.click();
        }
        return checked;
      });
      checked += result.length;
      for (const block of result) {
        block.commands.forEach(command => commands.add(command));
        if (block.goals) partial.push({chapter: name, text: block.text});
      }
    }
    assert(checked >= 190, 'Audit must cover the complete generated book');
    // The text intentionally stops here to motivate propositional extensionality.
    assert.equal(partial.length, 1, 'All other finished proofs must end without goals');
    assert.equal(partial[0].chapter, 'sets-functions');
    assert(partial[0].text.endsWith('have hx : S x ↔ T x := h x'));
    for (const command of ['expand', 'dsimp', 'simp', 'symm', 'ext', 'indisc',
      'rw', 'have', 'replace', 'let', 'suffices', 'apply', 'constructor', 'unpack', 'arith']) {
      assert(commands.has(command), `Audit must cover ${command}`);
    }
    assert.deepEqual(errors, []);
    console.log(`Reader step states passed: ${checked} book blocks, intermediate rewrites, pending goals, nested proofs.`);
  } finally { await browser.close(); }
}
main().catch(error => { console.error(error); process.exitCode = 1; });
