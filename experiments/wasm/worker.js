// Reuse the pinned runtime host and add the editor protocol without modifying it.
const originalImportScripts = self.importScripts.bind(self);
self.importScripts = (...urls) => {
  if (urls.some(url => /\/lean\.js(?:\?|$)/.test(url))) {
    const mark = stage => self.postMessage({type: 'profile', stage, at: performance.now()});
    const module = self.Module;
    const initialize = module.onRuntimeInitialized;
    module.onRuntimeInitialized = function (...args) {
      mark('native-initialize-start');
      // This is an embedded runtime, with no main() keeping it alive. An idle
      // pthread mailbox callback otherwise calls maybeExit() and destroys the
      // entire task pool between edits. The host terminates this Worker when
      // its lifetime ends, so hold one keepalive reference for that lifetime.
      runtimeKeepalivePush();
      const result = initialize.apply(this, args);
      mark('native-initialize-end');
      return result;
    };
    module.preRun = [() => mark('filesystem-start'), ...module.preRun, () => mark('filesystem-end')];
    mark('runtime-script-start');
    originalImportScripts(...urls);
    mark('runtime-script-end');
  } else originalImportScripts(...urls);
};
originalImportScripts('upstream-worker.js' + location.search);
const upstreamMessageHandler = self.onmessage;
self.onmessage = event => {
  if (event.data?.type !== 'goals') {
    upstreamMessageHandler(event);
    return;
  }
  try {
    if (typeof self.Module?._lean_wasm_goals !== 'function') {
      throw new Error('This runtime does not provide cursor-based goal queries');
    }
    const {line, character} = event.data;
    if (!Number.isSafeInteger(line) || !Number.isSafeInteger(character)
        || line < 0 || character < 0 || line > 0xffffffff || character > 0xffffffff) {
      throw new Error('Goal positions must be nonnegative UTF-16 coordinates');
    }
    const result = Module._lean_wasm_goals(line, character);
    const tag = Module.getValue(result + 7, 'i8') & 0xff;
    if (tag !== 0) {
      Module._lean_io_result_show_error(result);
      throw new Error('The Lean goal query failed');
    }
    self.postMessage({type: 'goals_result', success: true});
  } catch (error) {
    self.postMessage({type: 'goals_result', success: false, error: String(error)});
  }
};
