// Static browser fixtures: no preview server or Lean process is started.
const assert = require('node:assert/strict');
const fs = require('node:fs/promises');
const path = require('node:path');
let playwright;
try {playwright = require('playwright');}
catch {playwright = require(path.join(process.env.USERPROFILE, '.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright'));}
const root = path.resolve('_out/pages/foundations');

(async () => {
  const browser = await playwright.chromium.launch({channel:'chrome',headless:true});
  try {
    const context = await browser.newContext({isMobile:true,hasTouch:true,serviceWorkers:'block'});
    await context.route('https://book.test/**', async route => {
      try {
        const url = new URL(route.request().url());
        if (url.pathname === '/favicon.ico') return route.fulfill({status:204});
        let file = path.resolve(root, decodeURIComponent(url.pathname.slice(1)) || '.');
        if (file !== root && !file.startsWith(root + path.sep)) return route.fulfill({status:403});
        if ((await fs.stat(file)).isDirectory()) file = path.join(file, 'index.html');
        const mime = {'.html':'text/html; charset=utf-8','.js':'text/javascript','.css':'text/css',
          '.json':'application/json','.woff2':'font/woff2','.svg':'image/svg+xml'};
        await route.fulfill({contentType:mime[path.extname(file)] || 'application/octet-stream',body:await fs.readFile(file)});
      } catch {await route.fulfill({status:404});}
    });
    const page = await context.newPage();
    for (const width of [320,390,430]) {
      await page.setViewportSize({width,height:844});
      for (const slug of ['', 'proof/', 'sets-functions/', 'numbers-relations/', 'sizes/', 'tactics/', 'symbols/']) {
        await page.goto('https://book.test/' + slug, {waitUntil:'networkidle'});
        await page.evaluate(() => document.fonts.ready);
        const measure = () => page.evaluate(() => ({viewport:document.documentElement.clientWidth,
          document:document.documentElement.scrollWidth}));
        let bounds = await measure();
        assert(bounds.document <= bounds.viewport + 1, JSON.stringify({width,slug,...bounds}));
        if (slug === 'sizes/') {
          const tables = page.locator('.book-table-scroll');
          assert.equal(await tables.count(),2);
          for (const table of await tables.all()) {
            assert(await table.evaluate(node => node.scrollWidth > node.clientWidth));
            await table.evaluate(node => {node.scrollLeft = node.scrollWidth;});
          }
          bounds = await measure();
          assert(bounds.document <= bounds.viewport + 1, JSON.stringify({width,slug,scrolled:true,...bounds}));
          const steps = page.getByRole('button',{name:'단계 보기',exact:true}).first();
          await steps.click();
          bounds = await measure();
          assert(bounds.document <= bounds.viewport + 1, JSON.stringify({width,slug,steps:true,...bounds}));
        }
      }
    }
    console.log('PASS: seven reading pages at 320/390/430px; tables scroll locally and proof steps do not widen the page');
  } finally {await browser.close();}
})().catch(error => {console.error(error);process.exitCode=1;});
