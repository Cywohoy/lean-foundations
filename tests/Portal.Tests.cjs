const assert = require('node:assert/strict');
const fs = require('node:fs');
const http = require('node:http');
const path = require('node:path');
let playwright;
try { playwright = require('playwright'); }
catch { playwright = require(path.join(process.env.USERPROFILE, '.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright')); }
const root = path.resolve('_out/pages');
const prefix = '/lean-foundations/';
(async () => {
 const server = http.createServer((req,res) => {
  const url = new URL(req.url,'http://localhost');
  if (!url.pathname.startsWith(prefix)) { res.writeHead(404).end(); return; }
  let file = path.resolve(root,decodeURIComponent(url.pathname.slice(prefix.length)));
  if (file !== root && !file.startsWith(root+path.sep)) { res.writeHead(403).end(); return; }
  if (fs.existsSync(file) && fs.statSync(file).isDirectory()) file=path.join(file,'index.html');
  if (!fs.existsSync(file)) { res.writeHead(404).end(); return; }
  res.writeHead(200, {'Content-Type': {'.html':'text/html; charset=utf-8','.js':'text/javascript','.css':'text/css','.json':'application/json','.woff2':'font/woff2'}[path.extname(file)] || 'application/octet-stream'});
  fs.createReadStream(file).pipe(res);
 });
 await new Promise(resolve=>server.listen(0,'127.0.0.1',resolve));
 const base=`http://127.0.0.1:${server.address().port}${prefix}`;
 const browser=await playwright.chromium.launch({channel:'chrome',headless:true});
 try {
  const page=await browser.newPage();
  await page.goto(base);
  await page.evaluate(()=>document.fonts.ready);
  assert(await page.evaluate(()=>[...document.fonts].some(font=>font.family==='Pretendard' && font.status==='loaded')),
    'The portal must load its Pretendard font rather than silently use a fallback');
  assert(await page.evaluate(()=>[...document.fonts].some(font=>font.family==='NanumSquareNeo' && font.status==='loaded')),
    'The portal should load NanumSquareNeo headings');
  assert((await page.locator('h1').evaluate(node=>getComputedStyle(node).fontFamily)).startsWith('NanumSquareNeo'));
  assert.equal(await page.title(),'Lean으로 배우는 수학');
  assert.equal(await page.locator('meta[name="book-mode"]').count(),0);
  await page.getByRole('link',{name:'기초 수학',exact:true}).click();
  await page.waitForURL(base+'foundations/');
  assert.equal(await page.locator('meta[name="book-mode"]').getAttribute('content'),'wasm');
  // Existing drafts use the same problem key on the same origin after moving.
  await page.evaluate(()=>localStorage.setItem('lean-algebra.code.portal-route-test','saved proof'));
  await page.goto(base+'proof/?source=bookmark#proofs-assumptions-and-goals');
  await page.waitForURL(base+'foundations/proof/?source=bookmark#proofs-assumptions-and-goals');
  assert.equal(await page.evaluate(()=>localStorage.getItem('lean-algebra.code.portal-route-test')),'saved proof');
  await page.goto(base+'foundations/sets/subsets/');
  await page.waitForURL(/\/foundations\/sets-functions\/#sets-proving-universal-statements-and-implications$/);
  console.log('PASS: portal font, nested book, old bookmarks, query/hash preservation, and same-origin draft storage');
 } finally { await browser.close(); await new Promise(resolve=>server.close(resolve)); }
})().catch(error=>{console.error(error);process.exitCode=1;});
