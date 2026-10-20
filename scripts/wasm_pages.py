"""Stage a checksum-pinned browser runtime and translate book-only imports."""
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import tarfile
import urllib.request

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
    for name in ['lean-wasm.js', 'wasm-reader.js', 'exercise-model.js', 'unicode-input.js', 'lean-unicode.js']:
        shutil.copyfile(ROOT / 'assets/web' / name, site / 'assets/web' / name)
    shutil.copytree(ROOT / 'assets/web/vendor/lean-unicode-input', site / 'assets/web/vendor/lean-unicode-input', dirs_exist_ok=True)
    loader = importlib.util.spec_from_file_location('book_math_export', ROOT / 'scripts/book_code.py')
    exporter = importlib.util.module_from_spec(loader)
    loader.loader.exec_module(exporter)
    def translate(before):
        return exporter.translate(before)

    manifest_path = site / 'playground.json'
    manifest = json.loads(manifest_path.read_text(encoding='utf-8'))
    contexts_path = target / 'contexts.json'
    contexts = json.loads(contexts_path.read_text()) if contexts_path.is_file() else {}
    historical_keys = json.loads((ROOT / 'web/exercise-storage.json').read_text(encoding='utf-8'))
    exercise_names = set()
    for key, snippet in manifest.items():
        if snippet.get('exercise'):
            name = re.search(r'^theorem\s+(\w+)', snippet['code'], re.M)
            if not name or name[1] in exercise_names:
                raise ValueError('Exercises need distinct named declarations for stable saved work')
            exercise_names.add(name[1])
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
            snippet['before'] = ('import ' + context['module'] + '\nimport Ample.Tactic.Unfold\n\n'
                'register_expand_module AmpleBrowserContext\n' + context['scope'] + '\n')
        (site / 'playground' / (key + '.json')).write_text(json.dumps(snippet, ensure_ascii=False), encoding='utf-8')
    manifest_path.write_text(json.dumps(manifest, ensure_ascii=False), encoding='utf-8')
    return relative
