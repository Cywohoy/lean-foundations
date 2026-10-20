// Exercise the actual generated lookup function, including pthread catch-up indices.
const assert = require('node:assert/strict');
const fs = require('node:fs');
const vm = require('node:vm');
assert(process.argv[2], 'usage: node runtime-tests.cjs PATH/TO/OPTIMIZED/lean.js');
const source = fs.readFileSync(process.argv[2], 'utf8');
assert(source.includes('/* ample-dlsym-lazy-index */'), 'Pass an optimized runtime');
const start = source.indexOf('function __dlsym_js(');
const end = source.indexOf('__dlsym_js.sig=', start);
let enumerations = 0;
let additions = 0;
let error = '';
const registered = () => {};
const fresh = () => {};
const stub = Object.assign(() => {}, {stub: true});
const libraryExports = {registered, fresh, stub, data: 42};
Object.setPrototypeOf(libraryExports, {inherited: () => {}});
Object.defineProperty(libraryExports, 'hidden', {value: () => {}, enumerable: false});
const addresses = new Map([[registered, 123]]);
const heap = new Uint32Array(8);
const lookup = vm.runInNewContext(source.slice(start, end) + '\n__dlsym_js;', {
  Object: {prototype: Object.prototype, keys: object => { enumerations++; return Object.keys(object); }},
  LDSO: {loadedLibsByHandle: {0: {exports: libraryExports, name: 'main'}}},
  UTF8ToString: code => ['missing', 'registered', 'fresh', 'stub', 'data', 'hidden', 'inherited', 'later'][code],
  dlSetError: text => { error = text; },
  getFunctionAddress: fn => addresses.get(fn),
  addFunction: fn => { const address = 500 + additions++; addresses.set(fn, address); return address; },
  growMemViews: () => {}, HEAPU32: heap,
});
assert.equal(lookup(0, 0, 4), 0);
assert(error.includes('missing'));
assert.equal(lookup(0, 1, 4), 123);
assert.equal(lookup(0, 3, 4), 0);
assert.equal(lookup(0, 4, 4), 42);
assert.equal(lookup(0, 5, 4), 0);
assert.equal(lookup(0, 6, 4), 0);
assert.equal(enumerations, 0, 'No export scan is needed for these lookups');
assert.equal(lookup(0, 2, 4), 500);
assert.equal(heap[1], Object.keys(libraryExports).indexOf('fresh'));
assert.equal(enumerations, 1);
assert.equal(lookup(0, 2, 4), 500);
assert.equal(enumerations, 1, 'A registered function must not rescan exports');
// Export additions must use the current order, without a stale cached index.
libraryExports.later = () => {};
assert.equal(lookup(0, 7, 8), 501);
assert.equal(heap[2], Object.keys(libraryExports).indexOf('later'));
assert.equal(enumerations, 2);
assert.equal(additions, 2);
console.log('PASS: missing, hidden, inherited, stub, data, registered, new, and appended exports');
