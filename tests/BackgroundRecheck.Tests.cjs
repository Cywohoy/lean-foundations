const assert = require('node:assert/strict');
const fs = require('node:fs');
(async () => {
  global.crossOriginIsolated = true;
  global.window = new EventTarget();
  global.document = {querySelector: () => ({content:'.'})};
  global.fetch = async () => ({ok:true, json:async()=>({before:'',contextFiles:[]})});
  const compiled = [];
  global.fixtureRuntime = {
    boot:async()=>{}, addFiles:async()=>{},
    compile:async code=>{compiled.push(code);return {success:true,output:[]};},
    goalsAt:async()=>({found:true,goals:['current goal']})
  };
  const source = fs.readFileSync('assets/web/wasm-reader.js','utf8')
    .replace("import {createLeanRuntime} from './lean-wasm.js';", 'const createLeanRuntime = () => globalThis.fixtureRuntime;');
  const {createBrowserBackend} = await import('data:text/javascript;base64,'+Buffer.from(source).toString('base64'));
  const backend = createBrowserBackend(new URL('https://book.test/'));
  const foreground = await backend.call('/api/lean/check',{snippet:'first',code:'example : True := by trivial'});
  await backend.call('/api/lean/check',{snippet:'second',code:'example : False := by sorry',background:true});
  const state = await backend.call('/api/lean/goal',{session:foreground.session,version:foreground.version,position:{line:0,character:0}});
  assert.deepEqual(state.goal,['current goal']);
  assert(compiled.at(-1).includes('example : True'));
  console.log('PASS: background verification preserves the active editor session and restores its document for goals');
})().catch(error=>{console.error(error);process.exitCode=1;});
