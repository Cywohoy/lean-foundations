// Share the reader's own earlier proofs, never model solutions or later exercises.
export function declarations(code) {
  return [...code.matchAll(/^(?:(?:noncomputable|private|protected) )*(?:theorem|lemma|def)\s+([A-Za-z_][A-Za-z0-9_'.]*)/gm)]
    .map(match => match[1]);
}

export function earlierTheorems(manifest, current) {
  return Object.entries(manifest).filter(([, item]) => item.exerciseOrder < current.exerciseOrder)
    .sort((a, b) => b[1].exerciseOrder - a[1].exerciseOrder)
    .flatMap(([key, item]) => [...item.code.matchAll(/^(?:theorem|lemma)\s+(\w+)([\s\S]*?):= by\b/gm)]
      .map(match => ({key, name: [item.exerciseNamespace, match[1]].filter(Boolean).join('.'),
        reference: item.exerciseNamespace === current.exerciseNamespace ? match[1]
          : [item.exerciseNamespace, match[1]].filter(Boolean).join('.'),
        order: item.theoremOrder?.[match[1]],
        statement: match[2].trim(), declaration: match[2].trim(),
        exerciseChapter: item.exerciseChapter, exerciseNumber: item.exerciseNumber})));
}

// The name is displayed separately. Without binders, show just the proposition.
export function theoremSignature(item) {
  return (item.declaration || item.statement || '').trim().replace(/^:\s*/, '');
}

// Body theorems and prior exercises share the same chronology. A namespace or
// the fact that a proof was an exercise never grants it unconditional priority.
export function orderTheorems(items, preferredNames = []) {
  const preferred = new Set(preferredNames);
  const seen = new Set();
  return items.filter(item => {
    const name = item.name || item.reference;
    if (seen.has(name)) return false;
    seen.add(name);
    return true;
  }).map((item, index) => ({item, index,
    preferred: Boolean(item.preferred || preferred.has(item.name) || preferred.has(item.reference)
      || preferred.has(item.name?.split('.').at(-1))),
    order: Number.isFinite(item.order) ? item.order : -1,
  })).sort((a, b) => Number(b.preferred) - Number(a.preferred) || b.order - a.order || a.index - b.index)
    .map(({item}) => item);
}

function references(code) {
  // Comments and strings are not references. Lean block comments can nest.
  let text = '', depth = 0, quoted = false;
  for (let i = 0; i < code.length; ++i) {
    const pair = code.slice(i, i + 2);
    if (!quoted && pair === '/-') { ++depth; ++i; text += ' '; continue; }
    if (depth && pair === '-/') { --depth; ++i; continue; }
    if (depth) continue;
    if (!quoted && pair === '--') {
      const end = code.indexOf('\n', i);
      i = end < 0 ? code.length : end;
      text += '\n'; continue;
    }
    if (quoted && code[i] === '\\') { ++i; continue; }
    if (code[i] === '"') { quoted = !quoted; text += ' '; continue; }
    if (!quoted) text += code[i];
  }
  return new Set(text.match(/[A-Za-z_][A-Za-z0-9_'.]*/g) || []);
}

export function selectDependencies(manifest, current, code, draft) {
  const earlier = Object.entries(manifest).filter(([, item]) => item.exerciseOrder < current.exerciseOrder);
  const selected = new Map();
  function visit(source, order) {
    const used = references(source);
    for (const [key, item] of earlier) {
      if (item.exerciseOrder >= order || selected.has(key)) continue;
      if (!declarations(item.code).some(name => used.has(name)
          || used.has([item.exerciseNamespace, name].filter(Boolean).join('.')))) continue;
      const value = draft(item, key) ?? item.code;
      selected.set(key, {snippet: key, code: value});
      visit(value, item.exerciseOrder);
    }
  }
  visit(code, current.exerciseOrder);
  return [...selected.values()].sort((a, b) =>
    manifest[a.snippet].exerciseOrder - manifest[b.snippet].exerciseOrder);
}

export function closeScopes(source) {
  const scopes = [];
  for (const line of source.split('\n')) {
    const open = /^(?:namespace|section)(?:\s+(\S+))?\s*$/.exec(line);
    if (open) scopes.push(open[1] || '');
    else if (/^end(?:\s+\S+)?\s*$/.test(line)) scopes.pop();
  }
  return '\n' + scopes.reverse().map(name => `end${name ? ' ' + name : ''}\n`).join('');
}

export function scopeSource(snippet) {
  return snippet.before.replace(/^import [^\n]*\n?/gm, '').trim();
}

export function dependencyImports(current, previous) {
  const chapters = {proof:'Proof', 'sets-functions':'SetsFunctions',
    'numbers-relations':'NumbersRelations', sizes:'CardinalityChapter'};
  return [...new Set(previous.filter(item => item.exerciseChapter !== current.exerciseChapter)
    .map(item => 'import AmpleBrowserContext.Book.' + chapters[item.exerciseChapter]))];
}

export function guardedCode(snippet, code) {
  return snippet.exercise && snippet.allowedTactics
    ? code.replace(/^((?:theorem|lemma|example)\b[\s\S]*?:= by)\b/gm,
      (_, header) => `${header} learning_guard ${JSON.stringify(snippet.allowedTactics.join(','))} in`)
    : code;
}

export function dependencySource(snippet, code, guard = true) {
  const scope = guard ? scopeSource(snippet)
    : scopeSource(snippet).replace(/^register_expand_module[^\n]*\n?/gm, '');
  // Recreate each exercise's original namespace, variables and local settings.
  // Its mathematical definitions are already present in the current checked import.
  return 'section\n' + scope + '\n\n' + (guard ? guardedCode(snippet, code) : code)
    + '\n' + closeScopes(scope) + 'end\n\n';
}
