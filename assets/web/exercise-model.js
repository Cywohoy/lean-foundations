// Split checked textbook declarations into fixed context and editable tactic proofs.
// Complete helper definitions remain in place, including between dependent results.
export function exerciseModel(original, draft = original) {
  const declarations = [...original.matchAll(/^(?:(?:noncomputable|private|protected) )*(theorem|lemma|def|example)\b([^\n]*)/gm)];
  const parts = [];
  let cursor = 0;
  for (const [index, match] of declarations.entries()) {
    const next = declarations[index + 1]?.index ?? original.length;
    const text = original.slice(match.index, next);
    if (!/\bsorry\b/.test(text)) continue;
    const boundary = /:= by[^\S\n]*\n/.exec(text);
    if (!boundary) throw new Error('The exercise requires a multiline tactic proof.');
    const end = boundary.index + boundary[0].length;
    const raw = text.slice(end);
    const body = raw.trimEnd();
    const name = match[1] === 'example' ? `example_${parts.length + 1}` : match[2].trim().split(/\s|[({:]/)[0];
    parts.push({name, prefix: original.slice(cursor, match.index), header: text.slice(0, end),
      body: body || '  ', separator: raw.slice(body.length)});
    cursor = next;
  }
  if (!parts.length) throw new Error('No exercise declarations found.');
  const tail = original.slice(cursor);
  function parse(source) {
    const bodies = [];
    let cursor = 0;
    for (const [index, part] of parts.entries()) {
      const marker = part.prefix + part.header;
      if (!source.startsWith(marker, cursor)) return null;
      cursor += marker.length;
      const next = parts[index + 1];
      const end = next ? source.indexOf(next.prefix + next.header, cursor)
        : tail ? (source.endsWith(tail) ? source.length - tail.length : -1) : source.length;
      if (end < 0) return null;
      const body = source.slice(cursor, end).trimEnd();
      if (body.split('\n').some(line => line && !/^\s|^--/.test(line))) return null;
      bodies.push(body || '  ');
      cursor = end;
    }
    return bodies;
  }
  const bodies = parse(draft);
  return {
    parts, parse, bodies: bodies || parts.map(part => part.body), full: !bodies,
    editorBody(body) { return body.split('\n').map(line => line.startsWith('  ') ? line.slice(2) : line).join('\n'); },
    sourceBody(body) { return body.split('\n').map(line => '  ' + line).join('\n'); },
    source(values) { return parts.map((part, i) => part.prefix + part.header + values[i] + part.separator).join('') + tail; },
    start(values, index) {
      return parts.slice(0, index).reduce((n, part, i) =>
        n + part.prefix.length + part.header.length + values[i].length + part.separator.length, 0)
        + parts[index].prefix.length + parts[index].header.length;
    },
  };
}
