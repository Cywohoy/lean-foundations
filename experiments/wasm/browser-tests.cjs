const assert = require('node:assert/strict');
const fs = require('node:fs/promises');
const path = require('node:path');
const {createServer, ample} = require('./server.cjs');
let playwright;
try { playwright = require('playwright'); }
catch { playwright = require(path.join(process.env.USERPROFILE, '.cache/codex-runtimes/codex-primary-runtime/dependencies/node/node_modules/playwright')); }

async function main() {
  const useServiceWorker = process.argv.includes('--service-worker');
  const matchingToolchain = process.argv.includes('--matching-toolchain');
  const profileBoot = process.argv.includes('--profile-boot');
  const bootOnly = process.argv.includes('--boot-only');
  const basePath = process.argv.includes('--project-path') ? '/lean-algebra/wasm/' : '/';
  assert(!matchingToolchain || process.env.LEAN_WASM_ARTIFACTS, 'Set LEAN_WASM_ARTIFACTS for the matching build');
  const server = await createServer({isolate: !useServiceWorker, basePath});
  const browser = await playwright.chromium.launch({channel: 'chrome', headless: true});
  const report = {testedAt: new Date().toISOString(), browser: browser.version(), basePath, useServiceWorker, matchingToolchain, cases: []};
  try {
    const page = await browser.newPage();
    const proofRequests = [];
    page.on('request', request => {
      if (request.method() !== 'GET' || request.postData()) proofRequests.push(request.url());
    });
    page.on('pageerror', error => console.error('PAGE:', error.message));
    page.on('console', message => {
      if (['error', 'warning'].includes(message.type())) console.error('BROWSER:', message.text());
    });
    const url = `http://127.0.0.1:${server.address().port}${basePath}`;
    report.url = url;
    await page.goto(url);
    report.beforeServiceWorker = await page.evaluate(() => crossOriginIsolated);
    if (useServiceWorker) {
      assert.equal(report.beforeServiceWorker, false);
      await page.goto(url + '?coi');
      try {
        await page.waitForFunction(() => crossOriginIsolated && !!window.wasmExperiment);
      } catch (error) {
        report.serviceWorkerFailure = await page.evaluate(async () => ({
          url: location.href, isolated: crossOriginIsolated,
          controller: navigator.serviceWorker.controller?.scriptURL,
          registrations: (await navigator.serviceWorker.getRegistrations()).map(registration => ({
            scope: registration.scope, active: registration.active?.state,
          })),
        }));
        console.error('ISOLATION:', JSON.stringify(report.serviceWorkerFailure));
        throw error;
      }
    }
    report.isolated = await page.evaluate(() => crossOriginIsolated);
    assert.equal(report.isolated, true);
    const workerProfiler = profileBoot ? await page.context().newCDPSession(page) : null;
    // Worker profiling needs its own target session, not the page's session.
    if (workerProfiler) {
      await workerProfiler.send('Target.setAutoAttach', {autoAttach: true, waitForDebuggerOnStart: false, flatten: false});
      workerProfiler.on('Target.attachedToTarget', async ({sessionId, targetInfo}) => {
        if (targetInfo.type !== 'worker') return;
        const send = (id, method) => workerProfiler.send('Target.sendMessageToTarget',
          {sessionId, message: JSON.stringify({id, method})});
        await send(1, 'Profiler.enable');
        await send(2, 'Profiler.start');
        report.workerProfilerSession = sessionId;
      });
    }
    console.log('Booting the actual browser Worker…');
    report.boot = await page.evaluate(() => wasmExperiment.boot());
    console.log(`Ready: ${Math.round(report.boot.bootMs)} ms; phases: ${JSON.stringify(report.boot.timings)}`);
    if (workerProfiler && report.workerProfilerSession) {
      const profile = await new Promise(async (resolve, reject) => {
        const timer = setTimeout(() => reject(new Error('Worker profiler did not stop')), 10000);
        workerProfiler.on('Target.receivedMessageFromTarget', ({message}) => {
          const response = JSON.parse(message);
          if (response.id === 3) { clearTimeout(timer); resolve(response.result.profile); }
        });
        await workerProfiler.send('Target.sendMessageToTarget', {sessionId: report.workerProfilerSession,
          message: JSON.stringify({id: 3, method: 'Profiler.stop'})});
      });
      await fs.writeFile(path.resolve(__dirname, '../../tmp/wasm/boot-435.cpuprofile'), JSON.stringify(profile));
      await workerProfiler.detach();
    }
    if (bootOnly) return;

    const sets = await fs.readFile(path.join(ample, 'Ample/Math/Sets.lean'), 'utf8');
    // Named boundaries below keep the source sample independent of later custom tactics.
    const transStart = sets.indexOf('theorem subset_trans ');
    const transLastLine = sets.indexOf('exact hTUx hxT', transStart);
    const transEnd = transLastLine + 'exact hTUx hxT'.length;
    const publicSetSample = 'namespace Ample\n' + sets.slice(sets.indexOf('def Set ('), sets.indexOf('example : 3'))
      + sets.slice(sets.indexOf('def Subset '), sets.indexOf('theorem subset_refl'))
      + sets.slice(transStart, transEnd) + '\nend Ample';
    assert(transStart >= 0 && transLastLine > transStart, 'Ample sample boundaries changed');
    const cases = [
      ['implication', 'theorem sample (P Q : Prop) (h : P → Q) (hp : P) : Q := by\n  apply h\n  exact hp', 'ok'],
      ['arithmetic', 'example (n : Nat) : 2 * n ≠ 5 := by\n  omega', 'ok'],
      ['public-set-proof', publicSetSample, 'ok'],
      ['false-equality', 'example : 2 + 2 = 5 := by\n  rfl', 'error'],
      ['unfinished-goal', 'theorem sample (P Q : Prop) : P → Q := by\n  intro hp', 'error'],
      ['explicit-goal-trace', 'theorem sample (P : Prop) : P → P := by\n  intro hp\n  trace_state\n  exact hp', 'ok'],
      ['custom-macro', 'macro "finish_trivial" : tactic => `(tactic| exact True.intro)\nexample : True := by finish_trivial', 'probe'],
      ['lean-import', 'import Lean\n#check Lean.Elab.Tactic.evalTactic', matchingToolchain ? 'ok' : 'probe'],
      ['ample-classical', 'import Ample.Tactic.Classical\nopen Ample\nexample (P : Prop) (h : ¬¬P) : P := by\n  by_contra hn\n  exact h hn', matchingToolchain ? 'ok' : 'probe'],
    ];
    if (matchingToolchain) cases.push(
      ['platform', '#eval (System.Platform.numBits, System.Platform.isEmscripten)', 'ok'],
      ['ample-arith', 'import Ample\nopen Ample\nexample (n : Int) : 2 * n ≠ 5 := by\n  arith', 'ok'],
      ['ample-expand', 'import Ample\nopen Ample\nexample (n : Nat) (h : 0 < n) : n ∈ positives := by\n  expand\n  expand\n  exact h', 'ok'],
      ['ample-ext', 'import Ample\nopen Ample\nexample (S T : Set Nat) (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := by\n  ext x\n  exact h x', 'ok'],
      ['ample-auto', 'import Ample\nopen Ample\nopen scoped Ample.Auto\nexample (n : Int) (h : ¬ n < 0) : 0 ≤ n := by\n  exact h', 'ok'],
      ['ample-indisc', 'import Ample\nopen Ample\nexample (a b c d : Nat) (h : (a, b) = (c, d)) : a = c := by\n  indisc at h with ha hb\n  exact ha', 'ok'],
      ['ample-card', 'import Ample\nopen Ample\nexample (A B : Type) (h : SameCardinality A B) : cardinal A = cardinal B := by\n  card', 'ok'],
    );
    for (const [name, code, expect] of cases) {
      console.log(`Running: ${name}`);
      const result = await page.evaluate(code => wasmExperiment.compile(code), code);
      const diagnostics = result.output.flatMap(line => { try { return [JSON.parse(line)]; } catch { return []; } });
      const errors = diagnostics.filter(item => item.severity === 'error');
      const accepted = result.success && errors.length === 0;
      report.cases.push({name, code, ...result, accepted, diagnostics});
      console.log(JSON.stringify({name, accepted, ms: Math.round(result.wallMs), output: result.output}));
      if (expect === 'ok') assert(accepted, `${name} rejected`);
      if (expect === 'error') assert(!accepted, `${name} was incorrectly accepted`);
      if (name === 'unfinished-goal') assert(result.output.join('\n').includes('⊢ Q'));
      if (name === 'explicit-goal-trace') assert(result.output.join('\n').includes('⊢ P'));
      if (name === 'ample-classical' && !matchingToolchain) assert(result.output.join('\n').includes('incompatible header'));
      if (name === 'platform') assert(result.output.join('\n').includes('(32, true)'));
    }
    if (matchingToolchain) {
      const code = 'theorem cursor_test (P : Prop) : P → P := by\n  intro hp\n  exact hp\n';
      await page.evaluate(code => wasmExperiment.compile(code), code);
      const before = await page.evaluate(() => wasmExperiment.goalsAt(1, 2));
      const after = await page.evaluate(() => wasmExperiment.goalsAt(1, 10));
      const complete = await page.evaluate(() => wasmExperiment.goalsAt(2, 10));
      assert(before.found && before.goals.join('\n').includes('⊢ P → P'));
      assert(after.found && after.goals.join('\n').includes('hp : P'));
      assert(after.goals.join('\n').includes('⊢ P'));
      assert(complete.found && complete.goals.length === 0);
      report.cursorQueries = {before, after, complete};
      await page.locator('#source').fill(code);
      await page.waitForFunction(() => document.querySelector('#status').textContent === 'Checked', null, {timeout: 30000});
      await page.locator('#source').evaluate(input => {
        const position = input.value.indexOf('intro hp') + 'intro hp'.length;
        input.setSelectionRange(position, position);
        input.dispatchEvent(new MouseEvent('click', {bubbles: true}));
      });
      await page.waitForFunction(() => document.querySelector('#goal-state').textContent.includes('hp : P'), null, {timeout: 10000});
      await page.locator('#source').fill('theorem cursor_test (P : Prop) : P → P := by\n  ');
      await page.waitForFunction(() => document.querySelector('#status').textContent === 'Unfinished proof', null, {timeout: 30000});
      await page.waitForFunction(() => document.querySelector('#goal-state').textContent.includes('⊢ P → P'), null, {timeout: 10000});
      await page.locator('#source').fill('theorem cursor_test (P : Prop) : P → P := by\n  sorry\n');
      await page.waitForFunction(() => document.querySelector('#status').textContent === 'Unfinished proof'
        && /declaration uses [`']sorry[`']/.test(document.querySelector('#output').textContent), null, {timeout: 30000});
      report.editorAutoChecking = true;
    }
    assert.deepEqual(proofRequests, [], 'Proof text must not be submitted to the static server');
    report.proofSubmissionRequests = proofRequests;
  } finally {
    const out = path.resolve(__dirname, `../../tmp/wasm/browser-results${matchingToolchain ? '-435' : ''}${useServiceWorker ? '-sw' : ''}${bootOnly ? '-boot' : ''}.json`);
    await fs.writeFile(out, JSON.stringify(report, null, 2) + '\n');
    await browser.close();
    server.closeAllConnections();
    await new Promise(resolve => server.close(resolve));
    console.log(`Report: ${out}`);
  }
}
main().catch(error => { console.error(error); process.exitCode = 1; });
