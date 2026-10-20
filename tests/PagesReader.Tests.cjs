/* Exercise the static reader below the repository prefix used by GitHub Pages. */
const assert = require('node:assert/strict');
const fs = require('node:fs/promises');
const http = require('node:http');
const path = require('node:path');
let playwright;
try { playwright = require('playwright'); }
catch { playwright = require(path.join(process.env.USERPROFILE, '.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright')); }
const root = path.resolve(__dirname, '../_out/pages/foundations');
const prefix = '/lean-foundations/';
const mime = {'.html': 'text/html; charset=utf-8', '.js': 'text/javascript',
  '.css': 'text/css', '.json': 'application/json', '.woff2': 'font/woff2', '.svg': 'image/svg+xml'};

async function main() {
  const server = http.createServer(async (req, res) => {
    try {
      const url = new URL(req.url, 'http://localhost');
      if (url.pathname === '/favicon.ico') { res.writeHead(204).end(); return; }
      if (!url.pathname.startsWith(prefix)) { res.writeHead(404).end(); return; }
      let filename = path.resolve(root, decodeURIComponent(url.pathname.slice(prefix.length)) || '.');
      if (filename !== root && !filename.startsWith(root + path.sep)) { res.writeHead(403).end(); return; }
      if ((await fs.stat(filename)).isDirectory()) filename = path.join(filename, 'index.html');
      res.writeHead(200, {'Content-Type': mime[path.extname(filename)] || 'application/octet-stream'});
      res.end(await fs.readFile(filename));
    } catch { res.writeHead(404).end(); }
  });
  await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
  const base = process.env.BOOK_URL || `http://127.0.0.1:${server.address().port}${prefix}`;
  const browser = await playwright.chromium.launch({headless: true,
    executablePath: process.env.CHROME_PATH || (process.platform === 'win32' ? 'C:/Program Files/Google/Chrome/Application/chrome.exe' : undefined)});
  try {
    const context = await browser.newContext({permissions: ['clipboard-read', 'clipboard-write']});
    const page = await context.newPage();
    const failures = [];
    const apiRequests = [];
    page.on('pageerror', error => failures.push(error.message));
    page.on('response', response => { if (response.status() >= 400) failures.push(response.url()); });
    page.on('request', request => { if (request.url().includes('/api/lean/')) apiRequests.push(request.url()); });
    await page.goto(base + 'sets-functions/');
    await page.evaluate(() => document.fonts.ready);
    const proof = page.locator('.book-example').filter({hasText: '@[ext] theorem set_ext'});
    await proof.locator('.tactic > label').filter({hasText: /^funext x$/}).click();
    assert.ok((await proof.locator('.book-step-state').innerText()).includes('S x = T x'));
    assert.ok(await proof.getByRole('button', {name: '단계 보기', exact: true}).isVisible());
    await page.evaluate(() => document.activeElement?.blur());
    await page.mouse.move(0, 0);
    await page.waitForFunction(() => getComputedStyle(document.querySelector('.book-example:has(.book-step-state) .book-copy')).opacity === '1');
    await proof.hover();
    const copyBefore = await proof.getByRole('button', {name: '복사', exact: true}).boundingBox();
    await proof.getByRole('button', {name: '복사', exact: true}).click();
    await page.waitForFunction(() => document.body.textContent.includes('복사됨'));
    assert.deepEqual(await proof.getByRole('button', {name: '복사', exact: true}).boundingBox(), copyBefore);
    assert.ok((await page.evaluate(() => navigator.clipboard.readText())).includes('theorem set_ext'));
    // Each nested proof exposes its own goal, inner steps, and return state.
    await page.goto(base + 'sets-functions/');
    const trans = page.locator('.book-example').filter({hasText: 'theorem subset_trans '});
    await trans.getByRole('button', {name: '단계 보기', exact: true}).click();
    const titles = [];
    const states = [];
    for (;;) {
      titles.push(await trans.locator('.book-step-title').innerText());
      states.push(await trans.locator('.book-step-state').innerText());
      if (await trans.getByRole('button', {name: '다음 →', exact: true}).isDisabled()) break;
      await trans.getByRole('button', {name: '다음 →', exact: true}).click();
      if (titles.length > 20) throw new Error('Unexpected step sequence');
    }
    assert.equal(titles.filter(title => title === 'by').length, 2);
    for (const [inner, goal, name] of [
      ['exact hST x hx', '⊢ x ∈ T', 'hxT'],
    ]) {
      const at = titles.indexOf(inner);
      assert.ok(at > 0, `Missing subproof step: ${inner}`);
      assert.ok(states[at - 1].includes(goal), states[at - 1]);
      assert.equal(states[at], '보조 증명 완료');
      assert.ok(titles[at + 1].startsWith(`have ${name}`));
      assert.ok(states[at + 1].includes(name) && states[at + 1].includes('⊢ x ∈ U'));
    }
    assert.equal(titles.filter(title => title.startsWith('have ')).length, 1);
    assert.equal(titles.at(-1), 'exact hTU x hxT');
    await page.goto(base + 'foundations/relations/equivalence-relations/');
    await page.waitForURL(base + 'numbers-relations/#preliminaries-equivalence-relations');
    await page.goto(base + 'foundations/cardinality/same-cardinality/#cardinality-quotient-type');
    await page.waitForURL(base + 'sizes/#cardinality-quotient-type');
    await page.goto(base + 'foundations/functions/elements/#functions-fin');
    await page.waitForURL(base + 'sizes/#functions-fin');
    assert.ok(await page.locator('#functions-fin').isVisible());
    await page.goto(base + 'numbers-relations/');
    const exercise = page.locator('.book-exercise-card').filter({hasText: 'exercise_congruent_divisor'});
    assert.equal(await exercise.locator('.book-problem-caption').innerText(), '(법의 배수와 합동)');
    const questions = await exercise.locator(':scope > p').allTextContents();
    assert.equal(questions.length, 2);
    assert.ok(questions[0].trim().startsWith('(1)'));
    assert.ok(questions[1].trim().startsWith('(2)'));
    assert.equal(await exercise.locator('.book-exercise-statement > p').count(), 2);
    assert.ok((await exercise.locator('.book-exercise-heading').textContent()).includes('법의 배수와 합동'));

    for (const slug of ['proof','sets-functions','numbers-relations','sizes']) {
      await page.goto(base + slug + '/');
      const tree = page.locator('.book-toc-tree');
      assert.equal(await tree.count(),1);
      assert.equal(await tree.locator(':scope > li').count(),6);
      assert.equal(await tree.locator('[aria-current="page"]').count(),1);
      assert.equal(await page.locator('#toc .split-tocs').count(),0);
      const links = await tree.locator('[aria-current="page"] + ol a').evaluateAll(nodes => nodes.map(n=>n.href));
      assert(links.length > 5, slug);
      const sectionCount = await page.locator('main h2 .permalink-widget a').count();
      assert.equal(links.length, sectionCount, `Only major sections belong in the TOC: ${slug}`);
      assert.equal(await tree.locator('ol ol').count(), 0, slug);
      assert(links.every(href=>new URL(href).pathname.endsWith('/'+slug+'/')),slug);
      const missing = await page.evaluate(links=>links.filter(href=>!document.getElementById(decodeURIComponent(new URL(href).hash.slice(1)))),links);
      assert.deepEqual(missing,[],slug);
      const target = await page.locator('main h2').nth(2).evaluate(heading => {
        const link = heading.querySelector('.permalink-widget a');
        return new URL(link.href).searchParams.get('name');
      });
      const urlBeforeScroll = page.url();
      await page.locator('main h2').nth(2).evaluate(heading => {
        window.scrollBy(0, heading.getBoundingClientRect().top - 60);
      });
      await page.waitForFunction(tag => {
        const link = document.querySelector('.book-toc-tree [aria-current="location"]');
        return link && decodeURIComponent(new URL(link.href).hash.slice(1)) === tag;
      }, target);
      assert.equal(page.url(), urlBeforeScroll, 'Reading must not rewrite the URL');
      assert.equal(await tree.locator('[aria-current="location"]').count(), 1);
      // A subsection inherits its containing major section's marker.
      const subsection = await page.evaluate(() => {
        const headings = [...document.querySelectorAll('main h2, main h3')];
        let section;
        for (const heading of headings) {
          if (heading.tagName === 'H2') section = heading;
          else if (section) {
            window.scrollBy(0, heading.getBoundingClientRect().top - 60);
            return new URL(section.querySelector('.permalink-widget a').href).searchParams.get('name');
          }
        }
        return null;
      });
      if (subsection) await page.waitForFunction(tag => {
        const link = document.querySelector('.book-toc-tree [aria-current="location"]');
        return link && decodeURIComponent(new URL(link.href).hash.slice(1)) === tag;
      }, subsection);
      await page.evaluate(() => window.scrollTo(0, 0));
      await page.waitForFunction(() => !document.querySelector('.book-toc-tree [aria-current="location"]'));

    }
    await page.goto(base + 'proof/');
    await page.screenshot({path:'tmp/reading-desktop.png'});
    await page.setViewportSize({width:390,height:844});
    await page.screenshot({path:'tmp/reading-mobile.png'});
    assert(await page.evaluate(()=>document.documentElement.scrollWidth<=innerWidth+1),'Mobile body overflow');

    assert.deepEqual(apiRequests, []);
    assert.deepEqual(failures, []);
    console.log('PASS: static proof steps, clipboard, assets, legacy redirects, and no Lean server requests.');
  } finally {
    await browser.close();
    server.closeAllConnections();
    await new Promise(resolve => server.close(resolve));
  }
}
main().catch(error => { console.error(error); process.exit(1); });
