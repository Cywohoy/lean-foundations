const assert = require('node:assert/strict');
const fs = require('node:fs');

(async () => {
  const source = fs.readFileSync('assets/web/exercise-model.js', 'utf8');
  const {exerciseModel} = await import('data:text/javascript;base64,' + Buffer.from(source).toString('base64'));
  const manifest = JSON.parse(fs.readFileSync('_out/pages/foundations/playground.json', 'utf8'));
  const exercises = Object.values(manifest).filter(item => item.exercise);
  assert(exercises.length > 50);
  let proofs = 0;
  for (const item of exercises) {
    const model = exerciseModel(item.code);
    proofs += model.parts.length;
    assert(!model.full);
    assert.equal(model.editorBody(model.parts[0].body), 'sorry');
    const nested = 'constructor\n· intro h\n  exact h';
    assert.equal(model.editorBody(model.sourceBody(nested)), nested);
    assert.deepEqual(model.parse(model.source(model.bodies)), model.bodies);
    for (let i = 0; i < model.parts.length; ++i) {
      const code = model.source(model.bodies);
      assert(code.slice(model.start(model.bodies, i)).startsWith(model.parts[i].body));
    }
    // Keep blank proof indentation and trailing lines: cursor offsets depend on it.
    model.bodies[0] = '  \n  ';
    const code = model.source(model.bodies);
    assert(code.includes(':= by\n  \n  '));
    if (model.parts.length > 1) assert.equal(code.slice(model.start(model.bodies, 1), model.start(model.bodies, 1) + 7), '  sorry');
    assert.equal(model.parse(code.replace(model.parts[0].header, 'theorem changed : True := by\n')), null);
    const saved = exerciseModel(item.code, 'def helper := 1\n' + code);
    assert(saved.full, 'A noncanonical draft must remain intact in complete-code mode');
  }
  assert(proofs > 90);
  console.log(`PASS: all ${exercises.length} exercise blocks / ${proofs} proofs, fixed helper definitions, subproof offsets, and drafts`);
})().catch(error => { console.error(error); process.exitCode = 1; });
