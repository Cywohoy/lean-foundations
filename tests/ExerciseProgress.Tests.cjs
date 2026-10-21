/* Progress presentation and resume navigation; runtime validity is tested separately. */
const assert = require('node:assert/strict');
const fs = require('node:fs/promises');
const path = require('node:path');
let playwright;
try { playwright = require('playwright'); }
catch { playwright = require(path.join(process.env.USERPROFILE, '.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright')); }
const root = path.resolve(__dirname, '../_out/pages/foundations');
const prefix = '/lean-foundations/';
const mime = {'.html': 'text/html; charset=utf-8', '.js': 'text/javascript',
  '.css': 'text/css', '.json': 'application/json', '.woff2': 'font/woff2', '.svg': 'image/svg+xml'};

async function main() {
  // Browser-local fixtures avoid starting a preview server or opening a port.
  const base = `https://lean-foundations.test${prefix}`;
  const browser = await playwright.chromium.launch({headless: true,
    executablePath: process.env.CHROME_PATH || (process.platform === 'win32' ? 'C:/Program Files/Google/Chrome/Application/chrome.exe' : undefined)});
  try {
    const context = await browser.newContext({permissions: ['clipboard-read', 'clipboard-write'], serviceWorkers:'block'});
    await context.route('https://lean-foundations.test/**', async route => {
      try {
        const url = new URL(route.request().url());
        if (url.pathname === '/favicon.ico') return route.fulfill({status:204});
        if (!url.pathname.startsWith(prefix)) return route.fulfill({status:404});
        let filename = path.resolve(root, decodeURIComponent(url.pathname.slice(prefix.length)) || '.');
        if (filename !== root && !filename.startsWith(root + path.sep)) return route.fulfill({status:403});
        if ((await fs.stat(filename)).isDirectory()) filename = path.join(filename, 'index.html');
        await route.fulfill({status:200, contentType:mime[path.extname(filename)] || 'application/octet-stream',
          body:await fs.readFile(filename)});
      } catch { await route.fulfill({status:404}); }
    });
    const page = await context.newPage();
    // Seed previously checked results to exercise navigation and presentation.
    // Real proof validity and updates are checked by BrowserReader.Tests.cjs.
    await context.route('**/assets/web/wasm-reader.js', route => route.fulfill({
      contentType:'text/javascript', body:`export function createBrowserBackend(){ return {call(path,payload){
        return new Promise(resolve=>{ (window.pendingChecks ||= []).push(()=>resolve({session:'fixture',version:1,
          goal:[],goalNote:'',diagnostics:[],contextErrors:[],proofs:(payload.proofNames||[]).map(name=>({name,axioms:window.fixtureAxioms||[]}))})); });
      }} }`
    }));
    const manifest=JSON.parse(await fs.readFile(path.join(root,'playground.json'),'utf8'));
    const exercises=Object.entries(manifest).filter(([,v])=>v.exercise).sort((a,b)=>a[1].exerciseOrder-b[1].exerciseOrder);
    const proof=exercises.filter(([,v])=>v.exerciseChapter==='proof');
    async function seed(entries) {
      await page.evaluate(entries=>{
        for (const [,data,done] of entries) {
          const code=data.code.replace(/\bsorry\b/g,'exact True.intro');
          const total=(data.code.match(/^theorem\s+/gm)||[]).length;
          localStorage.setItem('lean-algebra.code.'+data.storageKey,code);
          localStorage.setItem('lean-algebra.result.'+data.storageKey,JSON.stringify({
            code,version:JSON.stringify([data.code,data.allowedTactics,data.contextFiles?.map(f=>f.sha256)]),
            done:done??total,total,parts:Array.from({length:total},(_,i)=>i<(done??total))
          }));
        }
      },entries);
    }
    async function count(expected) {
      await page.waitForFunction(expected=>document.querySelector('.book-progress-total')?.textContent===expected,expected);
    }
    const requests=[]; page.on('request',request=>requests.push(request.url()));
    await page.goto(base+'proof/');
    await count('0 / 62');
    assert(await page.evaluate(() => !!(document.querySelector('.book-toc-tree')
      .compareDocumentPosition(document.querySelector('.book-progress')) & Node.DOCUMENT_POSITION_FOLLOWING)),
      'Progress belongs below the table of contents');
    assert(!requests.some(url=>url.endsWith('/playground.json')),'Reading progress must not fetch the full execution manifest');
    assert.deepEqual(await page.locator('.book-chapter-progress').allTextContents(),['0/9','0/22','0/17','0/14']);
    const single=proof.find(([,v])=>(v.code.match(/^theorem\s+/gm)||[]).length===1);
    const partial=proof.find(([,v])=>(v.code.match(/^theorem\s+/gm)||[]).length>1);
    await seed([[...single,1],[...partial,1]]);
    await page.reload();
    await count('1 / 62');
    assert.equal(await page.locator('.book-toc-tree [aria-current="page"] .book-chapter-progress').innerText(),'1/9');
    const sectionTotal = await page.locator('.book-section-progress').allTextContents();
    assert.equal(sectionTotal.reduce((sum,text)=>sum+Number(text.split('/')[1]),0),proof.length);
    const section = page.locator(`.book-section-link[href$="#${single[1].exerciseSection}"]`);
    const sectionItems=proof.filter(([,data])=>data.exerciseSection===single[1].exerciseSection);
    assert.equal(await section.locator('.book-section-progress').innerText(),`1/${sectionItems.length}`);
    const card=page.locator(`[data-snippet="${partial[0]}"]`).locator('..');
    assert((await card.locator('.book-exercise-result').innerText()).startsWith('1/'));
    await page.locator('.book-progress-next').click();
    await page.waitForURL(new URL(`proof/#exercise-${partial[0]}`,base).href);
    assert(!await page.locator(`#exercise-${partial[0]} dialog`).isVisible(), 'Resume navigation only scrolls');
    await card.getByRole('button',{name:'이어서 풀기',exact:true}).click();
    await page.locator(`#exercise-${partial[0]} dialog`).waitFor({state:'visible'});
    assert.equal(await page.locator(`#exercise-${partial[0]} .book-proof-controls button`).first().getAttribute('data-complete'),'true');
    await page.setViewportSize({width:390,height:600});
    const workspace = page.locator(`#exercise-${partial[0]} dialog`);
    await workspace.locator('textarea').fill('sorry\n'.repeat(35));
    await workspace.evaluate(node=>{node.scrollTop=node.scrollHeight;});
    assert(await workspace.locator('.book-exercise-heading').evaluate(node=>{
      const rect=node.getBoundingClientRect(), dialog=node.closest('dialog').getBoundingClientRect();
      return rect.top>=dialog.top && rect.bottom<=dialog.bottom;
    }),'The return button must remain visible in a long, scrolled proof');
    await page.keyboard.press('Escape');
    await page.setViewportSize({width:1360,height:1000});
    await seed(proof.map(([key,data])=>[key,data]));
    await page.goto(base+'proof/');
    await count('9 / 62');
    const next=exercises.find(([,v])=>v.exerciseChapter==='sets-functions');
    await page.locator('.book-progress-next').click();
    await page.waitForURL(new URL(`sets-functions/#exercise-${next[0]}`,base).href);
    assert(!await page.locator(`#exercise-${next[0]} dialog`).isVisible(), 'Cross-chapter resume only scrolls');
    await page.keyboard.press('Escape');
    // A context-only update retains historical completion and rechecks without opening the problem.
    await page.addInitScript(() => Object.defineProperty(window, 'crossOriginIsolated', {value:true}));
    await page.evaluate(data=>{
      const key='lean-algebra.result.'+data.storageKey;
      const saved=JSON.parse(localStorage.getItem(key));
      saved.version=JSON.stringify([data.code,data.allowedTactics,['previous-context']]);
      localStorage.setItem(key,JSON.stringify(saved));
    },single[1]);
    await page.goto(base+'proof/');
    await count('9 / 62');
    await page.waitForFunction(key=>document.querySelector(`#exercise-${key}`)?.parentElement.querySelector('.book-exercise-result')?.textContent==='✓ 완료 · 재검사 대기',single[0]);
    await page.waitForFunction(()=>window.pendingChecks?.length>0);
    await page.evaluate(()=>window.pendingChecks.shift()());
    await page.waitForFunction(key=>document.querySelector(`#exercise-${key}`)?.parentElement.querySelector('.book-exercise-result')?.textContent==='✓ 완료',single[0]);
    await count('9 / 62');
    // A newly failing audit removes completion but never deletes the saved solution.
    await page.evaluate(data=>{
      const key='lean-algebra.result.'+data.storageKey;
      const saved=JSON.parse(localStorage.getItem(key));
      saved.version=JSON.stringify([data.code,data.allowedTactics,['another-context']]);
      localStorage.setItem(key,JSON.stringify(saved));
    },single[1]);
    await page.goto(base+'proof/');
    await page.evaluate(()=>{window.fixtureAxioms=['sorryAx'];});
    await page.waitForFunction(()=>window.pendingChecks?.length>0);
    await page.evaluate(()=>window.pendingChecks.shift()());
    await count('8 / 62');
    assert(await page.evaluate(data=>localStorage.getItem('lean-algebra.code.'+data.storageKey)?.includes('exact True.intro'),single[1]));
    await seed([[...single,1]]);
    await page.evaluate(id=>{
      const key='lean-algebra.result.'+id;
      const saved=JSON.parse(localStorage.getItem(key)); saved.version='old-context';
      localStorage.setItem(key,JSON.stringify(saved));
    },single[1].storageKey);
    await page.goto(base+'proof/');
    await count('8 / 62');
    assert.equal(await page.locator(`#exercise-${single[0]}`).locator('..').locator('.book-exercise-result').innerText(),'작성 중');
    const staleCard=page.locator(`#exercise-${single[0]}`).locator('..');
    await staleCard.getByRole('button',{name:'이어서 풀기',exact:true}).click();
    await page.keyboard.press('Escape');
    const other=await context.newPage();
    await other.goto(base+'tactics/');
    await other.evaluate(data=>{
      const key='lean-algebra.result.'+data.storageKey;
      const saved=JSON.parse(localStorage.getItem(key));
      saved.version=JSON.stringify([data.code,data.allowedTactics,data.contextFiles?.map(f=>f.sha256)]);
      localStorage.setItem(key,JSON.stringify(saved));
    },single[1]);
    await count('9 / 62');
    await page.waitForFunction(key=>document.querySelector(`#exercise-${key}`)?.parentElement.querySelector('.book-exercise-result')?.textContent==='✓ 완료',single[0]);
    await other.evaluate(data=>{
      const key='lean-algebra.code.'+data.storageKey;
      localStorage.setItem(key,localStorage.getItem(key).replace('exact True.intro','-- changed elsewhere\n  exact True.intro'));
    },single[1]);
    await count('8 / 62');
    await page.waitForFunction(key=>document.querySelector(`#exercise-${key} .book-draft-code`)?.textContent.includes('changed elsewhere'),single[0]);
    await staleCard.getByRole('button',{name:'이어서 풀기',exact:true}).click();
    assert((await staleCard.locator('textarea').inputValue()).includes('changed elsewhere'));
    await page.keyboard.press('Escape');
    await other.close();
    await page.setViewportSize({width:390,height:844});
    const overflow=await page.evaluate(()=>({width:document.documentElement.clientWidth,scroll:document.documentElement.scrollWidth}));
    assert(overflow.scroll<=overflow.width,JSON.stringify(overflow));
    await page.setViewportSize({width:1360,height:1000});
    await seed(exercises.map(([key,data])=>[key,data]));
    await page.goto(base);
    await count('62 / 62');
    assert.equal(await page.locator('.book-progress-next').innerText(),'모든 문제 완료');
    assert(await page.locator('.book-progress-next').isDisabled());
    assert.equal(await page.locator('.book-progress-storage').textContent(),'');
    const draftsBefore=await page.evaluate(()=>Object.fromEntries(Object.entries(localStorage)
      .filter(([key])=>key.startsWith('lean-algebra.code.'))));
    const reading=await context.newPage();
    await reading.goto(base+'proof/');
    await reading.waitForFunction(()=>document.querySelector('.book-progress-total')?.textContent==='62 / 62');
    const activeCard=reading.locator(`#exercise-${single[0]}`).locator('..');
    await activeCard.getByRole('button',{name:'풀이 보기',exact:true}).click();
    await reading.waitForFunction(()=>window.pendingChecks?.length>0);
    const legacyId=single[1].legacyKeys?.[0] || single[0];
    await page.evaluate(({legacyId})=>{
      localStorage.setItem('lean-algebra.code.'+legacyId,'legacy saved proof');
      localStorage.setItem('lean-algebra.code.other-book-proof','keep other book');
      localStorage.setItem('lean-algebra.result.other-book-proof','keep other result');
    },{legacyId});
    // Cancelling must not remove any saved work.
    page.once('dialog',dialog=>dialog.dismiss());
    await page.locator('.book-progress-reset').click();
    await count('62 / 62');
    assert.equal(await page.evaluate(id=>localStorage.getItem('lean-algebra.code.'+id),single[1].storageKey),
      draftsBefore['lean-algebra.code.'+single[1].storageKey]);
    page.once('dialog',dialog=>dialog.accept());
    await page.locator('.book-progress-reset').click();
    await count('0 / 62');
    assert.equal(await page.locator('.book-progress-storage').innerText(),'초기화됨');
    await reading.waitForFunction(()=>document.querySelector('.book-progress-total')?.textContent==='0 / 62');
    await reading.waitForFunction(()=>document.querySelector('dialog[open] textarea')?.value.trim()==='sorry');
    // An older in-flight verification must not restore the discarded solution.
    await reading.evaluate(()=>window.pendingChecks.shift()());
    await reading.waitForFunction(()=>document.querySelector('dialog[open] .book-primary')?.disabled===false);
    await reading.keyboard.press('Escape');
    await reading.waitForFunction(key=>document.querySelector(`#exercise-${key}`)?.parentElement
      .querySelector('.book-exercise-result')?.textContent==='',single[0]);
    assert.equal(await activeCard.locator('.book-draft-code').count(),0);
    assert.equal(await page.evaluate(id=>localStorage.getItem('lean-algebra.code.'+id),legacyId),null,
      'Legacy drafts must not restore erased work');
    assert.equal(await page.evaluate(()=>localStorage.getItem('lean-algebra.code.other-book-proof')),'keep other book');
    assert.equal(await page.evaluate(()=>localStorage.getItem('lean-algebra.result.other-book-proof')),'keep other result');
    assert.equal(await page.evaluate(()=>Object.keys(localStorage).filter(key=>key.startsWith('lean-algebra.result.')
      && key!=='lean-algebra.result.other-book-proof').length),0);
    assert.equal(await page.evaluate(id=>localStorage.getItem('lean-algebra.code.'+id),partial[1].storageKey),null);
    await page.reload();
    await count('0 / 62');
    assert.deepEqual(await page.locator('.book-chapter-progress').allTextContents(),['0/9','0/22','0/17','0/14']);
    await reading.close();
    await page.screenshot({path:'tmp/exercise-progress.png'});
    // Alternative methods have independent proof slots; applications that
    // reuse an exercise result share its checked compilation unit.
    for (const [name, parts] of [
      ['exercise_relation_specialization_apply', 2],
      ['exercise_inter_union_absorb', 2],
      ['exercise_cardinal_product', 4]
    ]) {
      const [key, data] = exercises.find(([,v])=>v.code.includes(`theorem ${name}`));
      await page.goto(base+data.exerciseChapter+'/');
      const card=page.locator(`#exercise-${key}`).locator('..');
      await card.getByRole('button',{name:'풀기',exact:true}).click();
      const dialog=page.locator(`#exercise-${key} dialog`);
      await dialog.waitFor({state:'visible'});
      await dialog.locator('.book-proof-controls button').last().waitFor({state:'visible'});
      assert.equal(await dialog.locator('.book-proof-controls button').count(),parts);
      await dialog.locator('.book-proof-controls button').last().click();
      assert.equal(await dialog.locator('textarea').getAttribute('aria-label'),`풀이 ${parts}`);
      await page.keyboard.press('Escape');
    }
    console.log('PASS: full reset and cancellation, active-editor and in-flight check reset across tabs, legacy draft cleanup, chapter/book counts, and resume links');
  } finally {
    await browser.close();
  }
}
main().catch(error => { console.error(error); process.exit(1); });
