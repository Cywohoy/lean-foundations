"""Select taught theorem names; Lean supplies their types and checks availability."""
import re
from book_code import CHAPTERS, ROOT

EXTERNAL = re.compile(r'\b(?:Nat|Int|Fin|Eq|Iff|And|Or|True|False|Classical)\.[A-Za-z_][A-Za-z0-9_.]*')


def chapter_names(chapter):
    source = (ROOT / 'AlgebraBook' / (chapter + '.lean')).read_text(encoding='utf-8')
    names, scopes = [], []
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
            elif shown:
                declaration = re.match(r'^(?:@\[[^\]]+\]\s*)?(?:protected\s+)?(?:theorem|lemma)\s+([^\s:(]+)', line)
                if declaration:
                    prefix = [name for kind, name in scopes if kind == 'namespace' and name]
                    names.append((offset, '.'.join([*prefix, declaration[1]])))
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
