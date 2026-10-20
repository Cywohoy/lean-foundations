import {createLeanRuntime} from './lean-wasm.js';
const statusNode = document.querySelector('#status');
const outputNode = document.querySelector('#output');
const sourceNode = document.querySelector('#source');
const goalNode = document.querySelector('#goal-state');
const runtime = createLeanRuntime(new URL('.', location.href), message => { statusNode.textContent = message; });
let ready = false;
async function boot() {
  const result = await runtime.boot();
  ready = true;
  document.querySelector('#check').disabled = false;
  return result;
}
const compile = code => runtime.compile(code);
const goalsAt = (line, character) => runtime.goalsAt(line, character);
fetch('runtime.json').then(response => response.json()).then(runtime => {
  document.querySelector('#runtime-note').textContent = `Lean ${runtime.version} — isolated browser experiment.`;
}).catch(() => {});

window.wasmExperiment = {boot, compile, goalsAt};
let checkedSource = null;
let usesSorry = false;
let checking = false;
let editTimer;

async function showCursorGoals() {
  if (runtime.pending || checking || checkedSource !== sourceNode.value) return;
  const cursor = sourceNode.selectionStart;
  const code = checkedSource;
  const before = sourceNode.value.slice(0, sourceNode.selectionStart);
  const rows = before.split('\n');
  try {
    const result = await goalsAt(rows.length - 1, rows.at(-1).length);
    if (code !== sourceNode.value || cursor !== sourceNode.selectionStart) {
      setTimeout(showCursorGoals, 0);
      return;
    }
    goalNode.textContent = result.found
      ? result.goals.length ? result.goals.join('\n\n') : usesSorry ? 'The proof contains a placeholder.' : 'No remaining goals.'
      : 'No proof state at this position.';
  } catch (error) { goalNode.textContent = String(error); }
}

async function checkEditor() {
  if (checking || !ready) return;
  if (runtime.pending) {
    editTimer = setTimeout(checkEditor, 100);
    return;
  }
  checking = true;
  const code = sourceNode.value;
  document.querySelector('#check').disabled = true;
  statusNode.textContent = 'Checking…';
  try {
    const result = await compile(code);
    if (code !== sourceNode.value) return;
    checkedSource = result.success ? code : null;
    const messages = result.output.flatMap(line => { try { return [JSON.parse(line)]; } catch { return []; } });
    const errors = messages.filter(message => message.severity === 'error');
    usesSorry = messages.some(message => message.kind === 'hasSorry'
      || /declaration uses [`']sorry[`']/.test(message.data || message.message || ''));
    const unfinished = errors.length && errors.every(message => message.kind === 'Tactic.unsolvedGoals');
    outputNode.textContent = messages.map(message => message.data || message.message).filter(Boolean).join('\n\n')
      || result.output.join('\n') || 'No diagnostics.';
    statusNode.textContent = !result.success ? 'Runtime error'
      : unfinished ? 'Unfinished proof' : errors.length ? `${errors.length} error(s)` : usesSorry ? 'Unfinished proof' : 'Checked';
  } catch (error) { statusNode.textContent = 'Failed'; outputNode.textContent = String(error); }
  finally {
    checking = false;
    document.querySelector('#check').disabled = false;
    if (code !== sourceNode.value) editTimer = setTimeout(checkEditor, 100);
    else await showCursorGoals();
  }
}

document.querySelector('#start').onclick = async () => {
  document.querySelector('#start').disabled = true;
  try { await boot(); await checkEditor(); }
  catch (error) { statusNode.textContent = 'Failed'; outputNode.textContent = String(error); }
};
document.querySelector('#check').onclick = checkEditor;
sourceNode.addEventListener('input', () => {
  if (!ready) return;
  clearTimeout(editTimer);
  goalNode.textContent = '';
  statusNode.textContent = 'Waiting for edits…';
  editTimer = setTimeout(checkEditor, 500);
});
sourceNode.addEventListener('click', showCursorGoals);
sourceNode.addEventListener('keyup', showCursorGoals);
