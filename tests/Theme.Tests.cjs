/* Static browser fixtures. No preview server or Lean process is started. */
const assert = require('node:assert/strict');
const fs = require('node:fs/promises');
const path = require('node:path');
let playwright;
try {playwright = require('playwright');}
catch {playwright = require(path.join(process.env.USERPROFILE, '.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright'));}
const root = path.resolve('_out/pages');
const artifacts = path.resolve('tmp/theme-tests');
const origin = 'https://book.test';
const key = 'lean-foundations.theme';

function luminance(rgb) {
  const channels = rgb.match(/[\d.]+/g).slice(0,3).map(Number).map(x => {
    x /= 255; return x <= .04045 ? x / 12.92 : ((x + .055) / 1.055) ** 2.4;
  });
  return .2126 * channels[0] + .7152 * channels[1] + .0722 * channels[2];
}
function contrast(a,b) {const x = luminance(a), y = luminance(b); return (Math.max(x,y)+.05)/(Math.min(x,y)+.05);}

(async () => {
  await fs.mkdir(artifacts,{recursive:true});
  const browser = await playwright.chromium.launch({channel:'chrome',headless:true});
  try {
    const context = await browser.newContext({colorScheme:'dark',serviceWorkers:'block',viewport:{width:1440,height:1000}});
    const errors = [];
    context.on('page', page => page.on('pageerror', error => errors.push(error.message)));
    await context.route(origin + '/**', async route => {
      try {
        const url = new URL(route.request().url());
        if (url.pathname === '/favicon.ico') return route.fulfill({status:204});
        let file = path.resolve(root,decodeURIComponent(url.pathname.slice(1)) || '.');
        if (file !== root && !file.startsWith(root+path.sep)) return route.fulfill({status:403});
        if ((await fs.stat(file)).isDirectory()) file = path.join(file,'index.html');
        const mime = {'.html':'text/html; charset=utf-8','.js':'text/javascript','.css':'text/css',
          '.json':'application/json','.woff2':'font/woff2','.svg':'image/svg+xml'};
        return route.fulfill({body:await fs.readFile(file),contentType:mime[path.extname(file)] || 'application/octet-stream'});
      } catch {return route.fulfill({status:404});}
    });
    const page = await context.newPage();
    // Capture the state as soon as the body exists: the saved/system choice
    // must be applied before any reading content, not just after DOM ready.
    await page.addInitScript(() => {
      const observer = new MutationObserver(() => {
        if (document.body && !window.firstBodyTheme) {
          window.firstBodyTheme = document.documentElement.dataset.theme;
          observer.disconnect();
        }
      });
      observer.observe(document,{childList:true,subtree:true});
    });
    const theme = () => page.locator('html').getAttribute('data-theme');
    const control = () => page.getByRole('combobox',{name:'테마',exact:true});
    const choose = value => control().selectOption(value);
    await page.goto(origin + '/foundations/proof/',{waitUntil:'networkidle'});
    assert.equal(await theme(),'dark');
    assert.equal(await page.evaluate(() => window.firstBodyTheme),'dark');
    assert.equal(await control().inputValue(),'system');
    assert.equal(await page.locator('[data-book-theme]').count(),1);
    const html = await fs.readFile(path.join(root,'foundations/proof/index.html'),'utf8');
    assert(html.indexOf('-verso-data/theme.js') < html.indexOf('rel="stylesheet"'), 'Bootstrap precedes styles');
    assert.match(html, /src="_reader\/[a-f0-9]+\/-verso-data\/theme.js"/);
    await page.emulateMedia({colorScheme:'light'});
    await page.waitForFunction(() => document.documentElement.dataset.theme === 'light');
    await choose('dark');
    await page.emulateMedia({colorScheme:'light'}); assert.equal(await theme(),'dark');
    assert.equal(await page.evaluate(key => localStorage.getItem(key),key),'dark');
    await page.reload({waitUntil:'networkidle'});
    assert.equal(await theme(),'dark');
    assert.equal(await page.evaluate(() => window.firstBodyTheme),'dark');

    const second = await context.newPage();
    await second.goto(origin,{waitUntil:'networkidle'});
    assert.equal(await second.locator('html').getAttribute('data-theme'),'dark');
    await second.getByRole('combobox',{name:'테마'}).selectOption('light');
    await page.waitForFunction(() => document.documentElement.dataset.theme === 'light');
    assert.equal(await control().inputValue(),'light');
    await choose('system');
    assert.equal(await theme(),'light');
    assert.equal(await page.evaluate(key => localStorage.getItem(key),key),null);
    await second.waitForFunction(() => document.querySelector('[data-book-theme]').value === 'system');
    await second.close();

    // Every actual reading page and the portal: native controls, content,
    // code and navigation remain legible and do not widen a narrow viewport.
    const slugs = ['', 'foundations/', ...['proof','sets-functions','numbers-relations','sizes','tactics','symbols'].map(x => 'foundations/'+x+'/')];
    const colors = [];
    await choose('dark');
    for (const slug of slugs) {
      await page.goto(origin+'/'+slug,{waitUntil:'networkidle'});
      assert.equal(await theme(),'dark',slug);
      assert.equal(await control().inputValue(),'dark',slug);
      const pair = await page.locator('body').evaluate(node => {
        const css=getComputedStyle(node); return {color:css.color,background:css.backgroundColor};
      });
      assert(contrast(pair.color,pair.background) >= 7,JSON.stringify({slug,...pair}));
      colors.push({slug,...pair});
      if (slug === 'foundations/proof/') {
        await page.getByRole('button',{name:'단계 보기',exact:true}).first().click();
        const panel = page.locator('.book-reader-panel:not([hidden])').first();
        await panel.waitFor({state:'visible'});
        assert((await panel.innerText()).length > 20);
        await page.screenshot({path:path.join(artifacts,'dark-proof.png')});
        // State and feedback samples use the exact classes from the live UI.
        await page.evaluate(() => {
          const fixture = document.createElement('section'); fixture.id='theme-contrast-fixture';
          fixture.innerHTML='<dialog open class="book-exercise-workspace"><div class="book-exercise-heading">문제</div><textarea class="book-code-input">intro h</textarea><p class="book-error">오류</p><p class="book-warning">미완료</p><p class="book-success">증명 완료</p><input class="book-theorems-search" placeholder="찾기"><pre class="book-live-goal">⊢ P</pre></dialog>';
          document.body.append(fixture);
        });
        for (const selector of ['.book-code-input','.book-error','.book-warning','.book-success','.book-theorems-search','.book-live-goal']) {
          const pair = await page.locator('#theme-contrast-fixture '+selector).evaluate(node => {
            let ancestor=node, background;
            while(ancestor) {background=getComputedStyle(ancestor).backgroundColor; if(background !== 'rgba(0, 0, 0, 0)') break; ancestor=ancestor.parentElement;}
            return {color:getComputedStyle(node).color,background};
          });
          assert(contrast(pair.color,pair.background)>=4.5,JSON.stringify({selector,...pair}));
        }
        await page.locator('#theme-contrast-fixture').evaluate(node=>node.remove());
      }
      for (const width of [320,390]) {
        await page.setViewportSize({width,height:844});
        assert(await control().isVisible(),slug);
        assert(await control().evaluate(node => {const b=node.getBoundingClientRect();return b.left>=0 && b.right<=innerWidth && b.height>=40;}),slug);
        assert(await control().evaluate(node => {const b=node.getBoundingClientRect();return document.elementFromPoint(b.x+b.width/2,b.y+b.height/2)===node;}),slug+' theme must not be covered by search');
        assert(await page.evaluate(() => document.documentElement.scrollWidth<=document.documentElement.clientWidth+1),slug+' at '+width);
        if (slug === 'foundations/proof/' && width === 320) {
          await page.locator('#toggle-toc-click').click();
          const title = page.locator('#toc .toc-title');
          await title.waitFor({state:'visible'});
          const colors = await title.evaluate(node => ({text:getComputedStyle(node.querySelector('h1')).color,
            background:getComputedStyle(document.querySelector('#toc')).backgroundColor}));
          assert(contrast(colors.text,colors.background)>=7,'Mobile book title must be legible: '+JSON.stringify(colors));
          await title.hover();
          assert.equal(await title.locator('h1').evaluate(node=>getComputedStyle(node).color),colors.text,'Hover must not restore the fixed black title color');
          await page.screenshot({path:path.join(artifacts,'dark-mobile-toc.png')});
          await page.locator('#toggle-toc-click').click();
          await page.setViewportSize({width:1024,height:900});
          assert(await title.isVisible(),'The tablet sidebar also displays the book title');
          assert.equal(await title.locator('h1').evaluate(node=>getComputedStyle(node).color),colors.text);
        }
      }
      if (slug === 'foundations/sets-functions/') await page.screenshot({path:path.join(artifacts,'dark-mobile.png')});
      if (slug === '') await page.screenshot({path:path.join(artifacts,'dark-portal.png')});
      await page.setViewportSize({width:1440,height:1000});
    }
    const redirect = await fs.readFile(path.join(root,'foundations/cardinality/index.html'),'utf8');
    assert(!redirect.includes('-verso-data/theme.'),'A legacy redirect has no reader-relative theme assets');
    await page.goto(origin+'/foundations/cardinality/',{waitUntil:'networkidle'});
    assert(new URL(page.url()).pathname.startsWith('/foundations/sizes/'));
    assert.equal(await theme(),'dark');
    await page.goto(origin+'/foundations/proof/',{waitUntil:'networkidle'});
    await page.setViewportSize({width:320,height:844});
    const search = page.getByRole('searchbox',{name:'본문 검색'});
    await search.fill('증명');
    const results = page.locator('#search-wrapper [role="listbox"]');
    await results.waitFor({state:'visible'});
    assert(await results.locator('li').count()>0);
    assert(await results.evaluate(node => {const b=node.getBoundingClientRect();return b.left>=0 && b.right<=innerWidth;}),'Search results fit beside the reserved theme slot');
    assert.equal(await results.evaluate(node=>getComputedStyle(node).backgroundColor),'rgb(32, 30, 27)');
    await search.press('Escape');
    await page.setViewportSize({width:1440,height:1000});
    await control().focus();
    assert.equal(await control().evaluate(node=>getComputedStyle(node).outlineStyle),'solid');
    await page.emulateMedia({media:'print'});
    assert.equal(await control().isVisible(),false);
    assert.equal(await page.locator('body').evaluate(node=>getComputedStyle(node).backgroundColor),'rgba(0, 0, 0, 0)');
    assert.notEqual(await page.locator('body').evaluate(node=>getComputedStyle(node).color),'rgb(231, 226, 218)');
    await page.emulateMedia({media:'screen'});
    await page.evaluate(()=>scrollTo(0,0));
    await choose('light');
    assert.equal(await page.locator('body').evaluate(node=>getComputedStyle(node).backgroundColor),'rgb(255, 255, 255)');
    await page.screenshot({path:path.join(artifacts,'light-proof.png')});
    // Invalid and blocked storage fall back to the system and remain interactive.
    await page.evaluate(key=>localStorage.setItem(key,'invalid'),key);
    await page.reload({waitUntil:'networkidle'}); assert.equal(await control().inputValue(),'system');
    await page.addInitScript(() => Object.defineProperty(window,'localStorage',{get(){throw new DOMException('Blocked','SecurityError');}}));
    await page.reload({waitUntil:'networkidle'});
    assert.equal(await control().inputValue(),'system');
    await choose('dark'); assert.equal(await theme(),'dark');
    assert.deepEqual(errors,[]);
    await fs.writeFile(path.join(artifacts,'colors.json'),JSON.stringify(colors,null,2));
    console.log('PASS: early theme bootstrap, system/manual choice, persistence, cross-tab/portal, blocked storage, all pages at 320/390px, contrast, keyboard, steps and light print');
  } finally {await browser.close();}
})().catch(error=>{console.error(error);process.exitCode=1;});
