"""Stage a checksum-pinned browser runtime and translate book-only imports."""
import hashlib
from html.parser import HTMLParser
import importlib.util
import json
from pathlib import Path
import re
import tarfile
import urllib.request
from urllib.parse import parse_qs, urlsplit

ROOT = Path(__file__).resolve().parents[1]


def prepare(site, bundle=None, download=False, config=None):
    spec = json.loads((config or ROOT / 'web/wasm-runtime.json').read_text(encoding='utf-8'))
    if download:
        cache = ROOT / 'tmp/wasm/downloads'
        cache.mkdir(parents=True, exist_ok=True)
        bundle = cache / (spec['sha256'] + '.tar.gz')
        if not bundle.exists():
            partial = bundle.with_suffix('.partial')
            with urllib.request.urlopen(spec['url'], timeout=120) as response, partial.open('wb') as output:
                while data := response.read(1024 * 1024):
                    output.write(data)
            partial.replace(bundle)
    with Path(bundle).open('rb') as stream:
        digest = hashlib.file_digest(stream, 'sha256').hexdigest()
    if digest != spec['sha256']:
        raise ValueError('Browser runtime checksum mismatch; no unverified runtime is staged')
    relative = 'wasm/' + digest[:16] + '/'
    target = site / relative
    target.mkdir(parents=True, exist_ok=True)
    with tarfile.open(bundle) as archive:
        archive.extractall(target, filter='data')
    for required in ['runtime/lean.js', 'runtime/lean.wasm', 'library.json', 'worker.js', 'upstream-worker.js']:
        if not (target / required).is_file():
            raise ValueError('Incomplete browser runtime: ' + required)
    import shutil
    shutil.copyfile(target / 'coi-serviceworker.js', site / 'coi-serviceworker.js')
    (site / 'assets/web').mkdir(parents=True, exist_ok=True)
    shutil.copyfile(ROOT / 'assets/web/reader.js', site / '-verso-data/reader.js')
    shutil.copyfile(ROOT / 'assets/web/reader.css', site / '-verso-data/reader.css')
    for name in ['lean-wasm.js', 'wasm-reader.js', 'exercise-model.js', 'exercise-context.js', 'unicode-input.js', 'lean-unicode.js']:
        shutil.copyfile(ROOT / 'assets/web' / name, site / 'assets/web' / name)
    shutil.copytree(ROOT / 'assets/web/vendor/lean-unicode-input', site / 'assets/web/vendor/lean-unicode-input', dirs_exist_ok=True)
    loader = importlib.util.spec_from_file_location('book_math_export', ROOT / 'scripts/book_code.py')
    exporter = importlib.util.module_from_spec(loader)
    loader.loader.exec_module(exporter)
    def translate(before):
        return exporter.translate(before)

    manifest_path = site / 'playground.json'
    manifest = json.loads(manifest_path.read_text(encoding='utf-8'))
    class ExerciseOrder(HTMLParser):
        def __init__(self):
            super().__init__()
            self.keys = []
            self.sections = {}
            self.section = None
            self.in_heading = False

        def handle_starttag(self, tag, attrs):
            attrs = dict(attrs)
            if tag == 'h2':
                self.in_heading = True
                self.section = attrs.get('id')
            elif self.in_heading and tag == 'a' and not self.section:
                self.section = parse_qs(urlsplit(attrs.get('href', '')).query).get('name', [None])[0]
            key = attrs.get('data-snippet')
            if key in manifest and manifest[key].get('exercise'):
                if not self.section:
                    raise ValueError('Exercise has no parent section: ' + key)
                self.keys.append(key)
                self.sections[key] = self.section

        def handle_endtag(self, tag):
            if tag == 'h2':
                self.in_heading = False

    ordered = []
    for chapter in ['proof', 'sets-functions', 'numbers-relations', 'sizes']:
        reader = ExerciseOrder()
        reader.feed((site / chapter / 'index.html').read_text(encoding='utf-8'))
        for number, key in enumerate(reader.keys, 1):
            manifest[key].update(exerciseChapter=chapter, exerciseSection=reader.sections[key], exerciseNumber=number,
                                 exerciseOrder=len(ordered))
            ordered.append(key)
    expected = {key for key, item in manifest.items() if item.get('exercise')}
    if len(ordered) != len(expected) or set(ordered) != expected:
        raise ValueError('Every exercise must appear exactly once in the reading order')
    contexts_path = target / 'contexts.json'
    contexts = json.loads(contexts_path.read_text()) if contexts_path.is_file() else {}
    historical_keys = json.loads((ROOT / 'web/exercise-storage.json').read_text(encoding='utf-8'))
    exercise_names = set()
    exercise_index = {}
    from learning_policy import exercise_policies
    from theorem_catalog import exercise_candidates, preferred_names
    policies = exercise_policies()
    theorem_candidates = exercise_candidates()
    for key, snippet in manifest.items():
        if snippet.get('exercise'):
            name = re.search(r'^theorem\s+(\w+)', snippet['code'], re.M)
            if not name or name[1] in exercise_names:
                raise ValueError('Exercises need distinct named declarations for stable saved work')
            exercise_names.add(name[1])
            snippet['allowedTactics'] = policies[name[1]]
            snippet['storageKey'] = 'exercise:' + name[1]
            snippet['legacyKeys'] = list(dict.fromkeys([key, *historical_keys.get(name[1], [])]))
        snippet['before'] = translate(snippet['before'])
        digest = hashlib.sha256(snippet['before'].encode()).hexdigest()
        if snippet.get('exercise') and digest not in contexts:
            raise ValueError('Missing checked browser context for ' + name[1]
                             + '; rebuild the exercise contexts and browser bundle before publishing')
        if snippet.get('exercise') and digest in contexts:
            context = contexts[digest]
            snippet['sourceBefore'] = snippet['before']
            snippet['contextFiles'] = [dict(item, url=relative + 'contexts/' + item['name'])
                                       for item in context['files']]
            preferred = preferred_names(snippet['code'])
            positions = {full_name: index for index, full_name in enumerate(theorem_candidates[name[1]])}
            snippet['theorems'] = [dict(item, preferred=item['reference'] in preferred
                                       or item['name'] in preferred,
                                       declaration=re.sub(r'^\S+\s*', '', item.get('declaration', item['statement'])))
                                  for item in context.get('theorems', []) if item['name'] in positions]
            snippet['theorems'].sort(key=lambda item: (not item['preferred'], -positions.get(item['name'], -1)))
            snippet['before'] = ('import ' + context['module'] + '\nimport Ample.Tactic.Unfold\nimport AmpleBrowserContext.LearningGuard\n\n'
                'register_expand_module AmpleBrowserContext\n' + context['scope'] + '\n')
            scopes = []
            for line in context['scope'].splitlines():
                opening = re.fullmatch(r'(namespace|section)(?:\s+(\S+))?\s*', line)
                if opening:
                    scopes.append((opening[1], opening[2]))
                elif re.fullmatch(r'end(?:\s+\S+)?\s*', line) and scopes:
                    scopes.pop()
            snippet['exerciseNamespace'] = '.'.join(name for kind, name in scopes if kind == 'namespace' and name)
        if snippet.get('exercise'):
            # Reading progress needs identities and versions, not every worked
            # example, import prefix, runtime file URL, or dependency source.
            fields = ['exercise', 'code', 'storageKey', 'legacyKeys', 'allowedTactics',
                      'exerciseChapter', 'exerciseSection', 'exerciseNumber', 'exerciseOrder', 'exerciseNamespace']
            exercise_index[key] = {field: snippet[field] for field in fields}
            exercise_index[key]['contextFiles'] = [{'sha256': item['sha256']}
                                                    for item in snippet['contextFiles']]
        (site / 'playground' / (key + '.json')).write_text(json.dumps(snippet, ensure_ascii=False), encoding='utf-8')
    manifest_path.write_text(json.dumps(manifest, ensure_ascii=False), encoding='utf-8')
    (site / 'exercises.json').write_text(json.dumps(exercise_index, ensure_ascii=False), encoding='utf-8')
    return relative
