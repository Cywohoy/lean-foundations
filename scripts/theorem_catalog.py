"""Select taught theorem names; Lean supplies their types and checks availability."""
import re
from book_code import CHAPTERS, ROOT

EXTERNAL = re.compile(r'\b(?:Nat|Int|Fin|Eq|Iff|And|Or|True|False|Classical)\.[A-Za-z_][A-Za-z0-9_.]*')


def signature_body(item):
    """Separate a checked declaration name from its binders and result type."""
    declaration = item.get('declaration')
    if not declaration:
        return item['statement'].strip()
    # ppSignature may append .{u_1, u_2}; whitespace can occur inside that list.
    prefix = re.match(re.escape(item['name']) + r'(?:\.\{[^}]*\})?(?=\s|:|$)', declaration)
    if not prefix:
        raise ValueError('Unexpected checked theorem signature: ' + item['name'])
    return declaration[prefix.end():].strip()


def chapter_names(chapter):
    source = (ROOT / 'AlgebraBook' / (chapter + '.lean')).read_text(encoding='utf-8')
    names, scopes = [], []
    prose = re.sub(r'^```[^\n]*\n.*?^```[^\n]*',
                   lambda match: ''.join('\n' if c == '\n' else ' ' for c in match[0]),
                   source, flags=re.M | re.S)
    introduced = {}
    for mention in re.finditer(r'`([A-Za-z_][A-Za-z0-9_.]*)`', prose):
        introduced.setdefault(mention[1], mention.start())
    # A displayed, checked type introduces its theorem just as a prose statement
    # does. A hidden #check without a corresponding output teaches nothing.
    checks = {m[1]: (m[2], m.start()) for m in re.finditer(
        r'^```lean[^\n]*\(name := (\w+)\)[^\n]*\n(?:set_option format\.width \d+ in\n)?#check ([A-Za-z_][A-Za-z0-9_.]*)\n```', source, re.M)}
    for output in re.finditer(r'^```leanOutput (\w+)\n(.*?)^```', source, re.M | re.S):
        if output[1] not in checks:
            continue
        name, position = checks[output[1]]
        displayed = re.match(r'([A-Za-z_][A-Za-z0-9_.]*)\s', output[2])
        if displayed and displayed[1].rsplit('.', 1)[-1] == name.rsplit('.', 1)[-1]:
            for spelling in (name, displayed[1]):
                introduced.setdefault(spelling, max(position, output.start()))
    visible = list(source)
    for match in re.finditer(r'^```(\w+)([^\n]*)\n(.*?)^```[^\n]*', source, re.M | re.S):
        kind, flags, body = match.group(1, 2, 3)
        retained = kind == 'savedLean' and '-keep' not in flags.split()
        shown = retained and '-show' not in flags.split()
        if not shown:
            visible[match.start():match.end()] = ['\n' if c == '\n' else ' ' for c in match.group()]
        if not retained:
            continue
        offset = match.start(3)
        for line in body.splitlines(keepends=True):
            opening = re.match(r'^(namespace|section)(?:\s+([^\s]+))?\s*$', line)
            if opening:
                scopes.append((opening[1], opening[2]))
            elif re.match(r'^end(?:\s+\S+)?\s*$', line):
                if scopes:
                    scopes.pop()
            else:
                declaration = re.match(r'^(?:@\[[^\]]+\]\s*)?(?:protected\s+)?(?:theorem|lemma)\s+([^\s:(]+)', line)
                if declaration:
                    prefix = [name for kind, name in scopes if kind == 'namespace' and name]
                    full_name = '.'.join([*prefix, declaration[1]])
                    if shown:
                        names.append((offset, full_name))
                    else:
                        # A repeated proof may be omitted after its result is
                        # stated in prose. Both introduction and declaration
                        # must precede an exercise that suggests the theorem.
                        positions = [introduced[name] for name in (declaration[1], full_name) if name in introduced]
                        if positions:
                            names.append((max(offset, min(positions)), full_name))
            offset += len(line)
    names.extend((m.start(), m.group().rstrip('.')) for m in EXTERNAL.finditer(''.join(visible)))
    return source, sorted(names)


def exercise_candidates():
    prior = []
    result = {}
    for chapter in CHAPTERS:
        source, names = chapter_names(chapter)
        for exercise in re.finditer(r'^theorem\s+(exercise_\w+)\b', source, re.M):
            taught = [name for position, name in names if position < exercise.start()]
            result[exercise[1]] = list(dict.fromkeys([*prior, *taught]))
        prior.extend(name for _, name in names)
    return result


def declaration_positions():
    """Place taught theorems and exercise results on one reading-order axis.

    Repeated uses do not reintroduce a theorem. Exercise names are unique in the
    manuscript; their short names can also be used by the reader's subproblems.
    Positions affect presentation only, never which proofs are available.
    """
    positions, offset = {}, 0
    for chapter in CHAPTERS:
        source, names = chapter_names(chapter)
        for position, name in names:
            positions.setdefault(name, offset + position)
        for exercise in re.finditer(r'^theorem\s+(exercise_\w+)\b', source, re.M):
            positions[exercise[1]] = offset + exercise.start()
        offset += len(source) + 1
    return positions


def preferred_names(code):
    """Find names explicitly cited in this problem's statement, not its solution."""
    name = re.search(r'^theorem\s+(exercise_\w+)\b', code, re.M)
    if not name:
        return set()
    for chapter in CHAPTERS:
        source = (ROOT / 'AlgebraBook' / (chapter + '.lean')).read_text(encoding='utf-8')
        position = source.find('theorem ' + name[1])
        if position >= 0:
            start = source.rfind('*문제 ', 0, position)
            return set(re.findall(r'`([A-Za-z_][A-Za-z0-9_.]*)`', source[start:position]))
    return set()
