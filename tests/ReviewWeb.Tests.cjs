/* Real review engine + browser UI, connected by request interception.
 * No TCP listener, preview server, or manuscript file is touched. */
const assert = require('node:assert/strict');
const fs = require('node:fs/promises');
const path = require('node:path');
const os = require('node:os');
const {spawnSync} = require('node:child_process');
let playwright;
try { playwright = require('playwright'); }
catch { playwright = require(path.join(process.env.USERPROFILE,
  '.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright')); }
const root = path.resolve(__dirname, '..');
const python = process.env.PYTHON || 'python';
const bridge = `import sys,json
sys.path.insert(0, sys.argv[1])
from review_state import ReviewStore, ReviewError
request=json.load(sys.stdin)
try:
 print(json.dumps(ReviewStore(sys.argv[2]).execute(request['action'],request.get('args',{}),request.get('revision')),ensure_ascii=False))
except ReviewError as ex:
 print(json.dumps({'error':str(ex)},ensure_ascii=False))
`;
async function main() {
  const temp = await fs.mkdtemp(path.join(os.tmpdir(), 'review-ui-'));
  let browser;
  try {
    spawnSync('git', ['init', '-q', temp]);
    await fs.writeFile(path.join(temp, '.gitignore'), 'review/local/\n');
    const source = '앞 문단\nBEGIN\n명제와 그 증명을 구별한다.\nEND\n뒤 문단\n';
    await fs.writeFile(path.join(temp, 'chapter.lean'), source);
    await fs.writeFile(path.join(temp, 'exercise.lean'), '앞에서 소개한 정리를 사용하는 문제.\n');
    await fs.mkdir(path.join(temp, 'review'));
    await fs.writeFile(path.join(temp, 'review/state.json'), JSON.stringify({schema:1,revision:0,units:{},dependencies:[],tasks:{},history:[]}));
    const call = (action, args = {}, revision) => {
      const process = spawnSync(python, ['-X','utf8','-c',bridge,path.join(root,'scripts'),temp], {input:JSON.stringify({action,args,revision}),encoding:'utf8'});
      assert.equal(process.status, 0, process.stderr);
      return JSON.parse(process.stdout);
    };
    for (const args of [
      {id:'book',title:'Lean으로 배우는 기초 수학',level:'book',checks:['structure']},
      {id:'proof',title:'1. 증명의 기초',level:'chapter',parent:'book',checks:['structure','boundary']},
      {id:'paragraph',title:'명제와 증명',level:'explanation',parent:'proof',sources:[{path:'chapter.lean',after:'BEGIN\n',before:'END\n'}],checks:['context','proof']},
      {id:'exercise',title:'함의의 연습문제',level:'exercise',parent:'proof',sources:[{path:'exercise.lean'}],checks:['exercise']}
    ]) assert.ok(!call('register', args).error);
    browser = await playwright.chromium.launch({headless:true,executablePath:process.env.CHROME_PATH || (process.platform === 'win32' ? 'C:/Program Files/Google/Chrome/Application/chrome.exe' : undefined)});
    const context = await browser.newContext({viewport:{width:1320,height:950},serviceWorkers:'block'});
    const errors = [];
    await context.route('**/*', async route => {
      const pathname = new URL(route.request().url()).pathname;
      if (pathname === '/api') {
        const req = route.request().postDataJSON(), data = call(req.action, req.args, req.revision);
        return route.fulfill({status:data.error ? 409 : 200,contentType:'application/json',body:JSON.stringify(data)});
      }
      const assets = {'/':['index.html','text/html'],'/app.js':['app.js','text/javascript'],'/style.css':['style.css','text/css']};
      if (!assets[pathname]) return route.fulfill({status:404,body:''});
      return route.fulfill({contentType:assets[pathname][1],body:await fs.readFile(path.join(root,'review/web',assets[pathname][0]))});
    });
    const page = await context.newPage(); page.on('pageerror', e => errors.push(e.message));
    await page.goto('http://review.test/#paragraph');
    await page.getByRole('heading',{name:'명제와 증명',exact:true}).waitFor();
    await page.locator('.source').waitFor();
    assert.match(await page.locator('.source').innerText(), /명제와 그 증명/);
    assert.equal(await page.locator('.check .unknown').count(), 2);

    await page.getByRole('button',{name:'문제 기록',exact:true}).first().click();
    await page.getByLabel('문제와 확인할 내용').fill('앞 문단과의 연결이 끊긴다.');
    await page.locator('#submit-dialog').click();
    await page.locator('dialog').waitFor({state:'hidden'});
    assert.equal(await page.locator('.check .dirty').count(), 1);

    await page.getByRole('button',{name:'검토 시작',exact:true}).first().click();
    await page.getByLabel('검토 근거').fill('앞뒤 문장을 함께 읽고 주어가 이어지는지 확인했다.');
    await page.getByLabel('검토자',{exact:true}).fill('검토자');
    await fs.writeFile(path.join(temp,'chapter.lean'),source.replace('구별한다','함께 살펴본다'));
    await page.locator('#submit-dialog').click();
    await page.locator('#form-error').waitFor({state:'visible'});
    assert.match(await page.locator('#form-error').innerText(), /바뀌/);
    assert.match(await page.getByLabel('검토 근거').inputValue(), /앞뒤 문장/);
    await page.getByRole('button',{name:'취소',exact:true}).click();
    await page.getByRole('button',{name:'변경 확인',exact:true}).click();
    await page.getByRole('button',{name:'검토 시작',exact:true}).first().click();
    await page.getByLabel('검토 근거').fill('수정된 문장과 앞뒤 문단을 다시 읽었다. 설명의 대상과 순서는 유지되었다.');
    await page.getByLabel('검토자',{exact:true}).fill('검토자');
    await page.locator('#submit-dialog').click();
    await page.locator('dialog').waitFor({state:'hidden'});
    assert.equal(await page.locator('.check .clean').count(), 1);
    assert.equal(await page.locator('.check .dirty').count(), 1); // proof remains dirty

    await page.getByRole('button',{name:'연결',exact:true}).click();
    await page.getByLabel('먼저 확인할 항목').selectOption('paragraph/context');
    await page.getByLabel('그 결과에 의존하는 항목').selectOption('exercise/exercise');
    await page.getByLabel('의존 이유').fill('문제에서 이 설명을 사용한다.');
    await page.locator('#submit-dialog').click();
    await page.locator('dialog').waitFor({state:'hidden'});
    assert.equal(call('status').state.units.exercise.checks.exercise.state,'dirty');

    await page.getByRole('button',{name:'이 범위에서 수정 작업',exact:true}).click();
    await page.getByLabel('작업 이름',{exact:true}).fill('예제 설명 보완');
    await page.getByLabel('수정 목적과 허용할 변경').fill('문단의 연결만 다듬는다.');
    await page.getByLabel('유지할 조건',{exact:true}).fill('예제 명제와 절 순서를 유지한다.');
    await page.locator('#submit-dialog').click();
    await page.locator('dialog').waitFor({state:'hidden'});
    assert.ok(Object.values(call('status').state.tasks).some(t=>t.status==='open'));
    await fs.writeFile(path.join(temp,'exercise.lean'),'범위 밖의 수정');
    await page.getByRole('button',{name:'변경 확인',exact:true}).click();
    await page.locator('.task-summary .violation').waitFor();
    await page.getByRole('button',{name:'작업 범위 확인',exact:true}).click();
    await page.getByLabel('상위 범위에서 검토를 멈추는 근거와 유지 조건 확인').fill('상위 설명은 유지된다.');
    await page.locator('#submit-dialog').click();
    await page.locator('#form-error').waitFor({state:'visible'});
    assert.match(await page.locator('#form-error').innerText(), /범위 밖/);
    await page.getByRole('button',{name:'취소',exact:true}).click();

    await page.getByRole('button',{name:'범위 추가',exact:true}).click();
    await page.getByLabel('이름',{exact:true}).fill('핵심 문장');
    await page.getByLabel('ID (영문·숫자·하이픈)').fill('sentence');
    await page.getByLabel('시작 경계 문구 (이 문구 다음부터)').fill('BEGIN\n');
    await page.getByLabel('끝 경계 문구 (이 문구 전까지)').fill('END\n');
    await page.locator('#submit-dialog').click();
    await page.locator('dialog').waitFor({state:'hidden'});
    assert.equal(call('status').state.units.sentence.checks.context.state,'unknown');
    await fs.writeFile(path.join(temp,'REVIEW_PROCESS.md'),'Check the placement of related tactic forms.');
    await page.getByRole('button',{name:'변경 확인',exact:true}).click();
    await page.locator('#protocol-notice').waitFor({state:'visible'});
    assert.match(await page.locator('#protocol-notice').innerText(), /검토 기준 변경.*남음/);
    const version = call('status').state;
    assert.ok(version.protocol_review.pending > 0);
    for (const [id,unit] of Object.entries(version.units)) {
      for (const aspect of Object.keys(unit.checks)) {
        if(id==='exercise') continue; // its explanation prerequisite is reviewed below first
        const check=id+'/'+aspect, ticket=call('prepare',{check}).result;
        assert.ok(!call('accept',{check,ticket,evidence:'Re-read with the updated placement criterion.',reviewer:'UI test'}).error);
      }
    }
    const check='exercise/exercise', ticket=call('prepare',{check}).result;
    assert.ok(!call('accept',{check,ticket,evidence:'Re-solved after reviewing the updated prerequisite.',reviewer:'UI test'}).error);
    await page.getByRole('button',{name:'변경 확인',exact:true}).click();
    await page.locator('#protocol-notice').waitFor({state:'hidden'});
    const output = path.join(root,'tmp/review-hierarchy-20261022'); await fs.mkdir(output,{recursive:true});
    await page.screenshot({path:path.join(output,'review-desktop.png'),fullPage:true});
    await page.setViewportSize({width:390,height:844});
    assert.ok(await page.evaluate(()=>document.documentElement.scrollWidth<=innerWidth),'Mobile horizontal overflow');
    await page.screenshot({path:path.join(output,'review-mobile.png'),fullPage:true});
    assert.deepEqual(errors,[]);
    console.log('Review web: state display, issue recording, stale review rejection, evidence retention, independent proof state, dependency linking, task scope enforcement, range creation, desktop/mobile layout passed. No server opened.');
  } finally {
    if (browser) await browser.close();
    assert.equal(path.dirname(path.resolve(temp)),path.resolve(os.tmpdir()));
    assert.ok(path.basename(temp).startsWith('review-ui-'));
    await fs.rm(temp,{recursive:true,force:true});
  }
}
main().catch(e=>{console.error(e);process.exitCode=1;});
