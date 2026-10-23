const assert = require('node:assert/strict');
const fs = require('node:fs');

(async () => {
  const source = fs.readFileSync('assets/web/exercise-context.js', 'utf8');
  const tools = await import('data:text/javascript;base64,' + Buffer.from(source).toString('base64'));
  assert.equal(tools.theoremSignature({declaration: ': parityClass 0 ≠ parityClass 1'}),
    'parityClass 0 ≠ parityClass 1');
  assert.equal(tools.theoremSignature({statement: '  :\n  True  '}), 'True');
  assert.equal(tools.theoremSignature({statement: '(P Q : Prop) (hP : P) : Q → P'}),
    '(P Q : Prop) (hP : P) : Q → P', 'Binder colons remain meaningful');
  assert.equal(tools.theoremSignature({statement: '∀ x : Nat, x = x'}), '∀ x : Nat, x = x');
  assert.equal(tools.theoremSignature({declaration: '', statement: 'True'}), 'True');
  const manifest = JSON.parse(fs.readFileSync('_out/pages/foundations/exercises.json', 'utf8'));
  const find = name => Object.entries(manifest).find(([, item]) => item.code.includes('theorem ' + name));
  const [previousKey, previous] = find('exercise_fin_succ_not_injective');
  const [, current] = find('exercise_fin_collision');
  assert.equal(previous.exerciseNumber, 3);
  assert.equal(current.exerciseNumber, 4);
  const proof = '  intro hf\n  have hle : n + 1 ≤ n := by\n    apply fin_injective_le f\n    exact hf\n  arith';
  const earlierDraft = previous.code.replace('  sorry', proof);
  const lookup = (item, key) => key === previousKey ? earlierDraft : null;
  const selected = tools.selectDependencies(manifest, current,
    'apply exercise_fin_succ_not_injective n f', lookup);
  assert.deepEqual(selected, [{snippet: previousKey, code: earlierDraft}]);
  assert.deepEqual(tools.selectDependencies(manifest, current,
    '-- exercise_fin_succ_not_injective\n/- outer /- inner -/ comment -/\ntrace "exercise_fin_succ_not_injective"', lookup), []);
  assert.deepEqual(tools.selectDependencies(manifest, previous, 'apply exercise_fin_collision', lookup), []);
  assert.deepEqual(tools.selectDependencies(manifest, current, 'apply Ample.exercise_fin_succ_not_injective', lookup), selected);
  assert.equal(tools.selectDependencies(manifest, current,
    'apply exercise_fin_succ_not_injective n f', () => null)[0].code, previous.code);
  const catalog = tools.earlierTheorems(manifest, current);
  assert(catalog.some(item => item.reference === 'exercise_fin_succ_not_injective'));
  assert(!catalog.some(item => item.reference === 'exercise_fin_collision'));
  const older = {name: 'ProofExamples.earlier', reference: 'ProofExamples.earlier', order: 10, statement: 'P'};
  const recent = {name: 'Ample.recent', reference: 'recent', order: 100, statement: 'Q'};
  const exercise = {name: 'Ample.exercise_prior', reference: 'exercise_prior', order: 80, statement: 'R'};
  assert.deepEqual(tools.orderTheorems([older, exercise, recent]), [recent, exercise, older],
    'Prior exercises and example namespaces do not outrank newer body theorems');
  assert.deepEqual(tools.orderTheorems([recent, older, exercise], ['ProofExamples.earlier']), [older, recent, exercise],
    'An explicit citation wins even when it comes from an earlier example namespace');
  assert.deepEqual(tools.orderTheorems([recent, exercise], ['Ample.exercise_prior']), [exercise, recent]);
  assert.deepEqual(tools.orderTheorems([recent, exercise], ['exercise_prior']), [exercise, recent]);
  const newerExample = {...older, order: 110};
  assert.deepEqual(tools.orderTheorems([recent, newerExample]), [newerExample, recent],
    'The namespace is also not penalized when its theorem is actually newer');
  assert.deepEqual(tools.orderTheorems([recent, {...recent, reference: 'Ample.recent'}]), [recent]);
  assert.deepEqual(tools.orderTheorems([{name:'preferred', preferred:true}, {name:'ordinary', order:200}])
    .map(item => item.name), ['preferred', 'ordinary']);
  const fullManifest = JSON.parse(fs.readFileSync('_out/pages/foundations/playground.json', 'utf8'));
  for (const [key, item] of Object.entries(fullManifest).filter(([, item]) => item.exercise)) {
    assert.deepEqual(manifest[key].theoremOrder, item.theoremOrder,
      'The lightweight dependency index carries prior exercises on the same reading-order axis');
    const combined = tools.orderTheorems([...item.theorems, ...tools.earlierTheorems(manifest, item)], item.preferredTheorems);
    for (const theorem of combined) {
      assert(!tools.theoremSignature(theorem).startsWith(':'), theorem.name);
      assert(tools.theoremSignature(theorem).trim(), theorem.name);
    }
    let previousOrder = Infinity, sawOrdinary = false;
    for (const theorem of combined) {
      const preferred = theorem.preferred || item.preferredTheorems.includes(theorem.name)
        || item.preferredTheorems.includes(theorem.reference)
        || item.preferredTheorems.includes(theorem.name.split('.').at(-1));
      assert(Number.isFinite(theorem.order));
      if (preferred) assert(!sawOrdinary, 'Cited results precede both exercise and body results');
      else if (!sawOrdinary) {sawOrdinary = true; previousOrder = Infinity;}
      assert(theorem.order <= previousOrder, 'Each priority group follows the same source chronology');
      previousOrder = theorem.order;
    }
  }
  const ordered = Object.entries(manifest).sort((a, b) => a[1].exerciseOrder - b[1].exerciseOrder);
  let references = 0;
  for (let i = 0; i + 1 < ordered.length; ++i) {
    const [key, item] = ordered[i];
    for (const name of tools.declarations(item.code)) {
      assert(tools.selectDependencies(manifest, ordered[i + 1][1], 'exact ' + name, () => null)
        .some(dependency => dependency.snippet === key), name);
      ++references;
    }
  }
  const graph = {
    a: {exerciseOrder: 0, code: 'theorem exercise_a : True := by\n  sorry', exerciseNamespace: 'A'},
    b: {exerciseOrder: 1, code: 'theorem exercise_b : True := by\n  sorry', exerciseNamespace: 'B'},
    c: {exerciseOrder: 2, code: 'theorem exercise_c : True := by\n  sorry', exerciseNamespace: 'B'},
  };
  assert.deepEqual(tools.selectDependencies(graph, graph.c, 'exact exercise_b', (item, key) =>
    key === 'b' ? item.code.replace('sorry', 'exact A.exercise_a') : null).map(item => item.snippet), ['a', 'b']);
  assert.equal(tools.earlierTheorems(graph, graph.b)[0].reference, 'A.exercise_a');
  assert.equal(tools.closeScopes('namespace A\nsection\nend\n'), '\nend A\n');
  const wrapped = tools.dependencySource({before: 'import Context\nnamespace A\n',
    exercise: true, allowedTactics: ['exact']}, 'theorem exercise_a : True := by\n  exact True.intro');
  assert(!wrapped.includes('import Context'));
  assert(wrapped.includes('namespace A\n'));
  assert(wrapped.includes('by learning_guard "exact" in\n'));
  assert(wrapped.endsWith('end A\nend\n\n'));
  assert.deepEqual(tools.dependencyImports({exerciseChapter:'sizes'}, [
    {exerciseChapter:'proof'}, {exerciseChapter:'sizes'}, {exerciseChapter:'proof'}]), ['import AmpleBrowserContext.Book.Proof']);
  console.log(`PASS: ${references} earlier declarations, saved drafts, unfinished fallbacks, transitive dependencies, namespaces, and chronological theorem lookup`);
})().catch(error => {console.error(error); process.exitCode = 1;});
