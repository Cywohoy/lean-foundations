"""Replace the compiler and matching libraries of a checksum-pinned base bundle.

This stages an unpublished runtime; it does not upload releases or change the
public pin. Build the matching toolchain and packs before invoking this script.
"""
import argparse
import hashlib
import io
import json
from pathlib import Path
import tarfile

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--base', type=Path, required=True)
parser.add_argument('--toolchain', type=Path, required=True)
parser.add_argument('--ample-lib', type=Path, required=True)
parser.add_argument('--packs', type=Path, required=True)
parser.add_argument('--ample-source', type=Path, help='Matching source snapshot when updating Ample')
parser.add_argument('--ample-commit', help='Full Git revision of the matching source snapshot')
parser.add_argument('--output', type=Path, required=True)
parser.add_argument('--config', type=Path, required=True)
args = parser.parse_args()
pin = json.loads((ROOT / 'web/wasm-base-runtime.json').read_text())
assert hashlib.file_digest(args.base.open('rb'), 'sha256').hexdigest() == pin['sha256']
assert 'ample-dlsym-lazy-index' in (args.toolchain / 'bin/lean.js').read_text()
source = args.toolchain.parents[2] / 'src/Lean/BrowserFrontend.lean'
frontend = (ROOT / 'web/lean/BrowserFrontend.lean').read_text(encoding='utf-8')
assert source.read_text(encoding='utf-8') == frontend, 'Install the checked frontend before building'
assert (args.toolchain / 'bin/lean.wasm').stat().st_mtime >= source.stat().st_mtime
manifest = json.loads((args.packs / 'library.json').read_text())
for pack in manifest['packs']:
    data = (args.packs / pack['file']).read_bytes()
    assert len(data) == pack['bytes'] and hashlib.sha256(data).hexdigest() == pack['sha256']
replacements = {'runtime/lean.js': args.toolchain / 'bin/lean.js',
                'runtime/lean.wasm': args.toolchain / 'bin/lean.wasm',
                'library.json': args.packs / 'library.json'}
replacements.update({'packs/' + pack['file']: args.packs / pack['file'] for pack in manifest['packs']})
args.output.parent.mkdir(parents=True, exist_ok=True)
with tarfile.open(args.base) as old, tarfile.open(args.output, 'w:gz', compresslevel=3) as new:
    metadata = json.load(old.extractfile('runtime.json'))
    assert metadata['ampleCommit'] == pin['ampleCommit']
    build = json.loads((args.ample_lib / 'ample-build.json').read_text())
    if args.ample_commit:
        assert args.ample_source and len(args.ample_commit) == 40
        for module in build['modules']:
            source_file = args.ample_source / (module['name'].replace('.', '/') + '.lean')
            assert hashlib.sha256(source_file.read_bytes()).hexdigest() == module['sourceSha256']
            compiled = args.ample_lib / (module['name'].replace('.', '/') + '.olean')
            assert hashlib.sha256(compiled.read_bytes()).hexdigest() == module['oleanSha256']
        metadata['ampleCommit'] = args.ample_commit
        metadata['ampleBuild'] = build
    else:
        assert metadata['ampleBuild'] == build
    metadata['browserFrontendSha256'] = hashlib.sha256(frontend.encode()).hexdigest()
    for entry in old:
        if args.ample_commit and entry.name == 'NOTICE.txt':
            notice = old.extractfile(entry).read().decode().replace(pin['ampleCommit'], args.ample_commit)
            data = notice.encode()
            entry.size = len(data)
            new.addfile(entry, io.BytesIO(data))
            continue
        if entry.name == 'runtime.json' or entry.name == 'contexts.json' or entry.name.startswith(('packs/', 'contexts/')) or entry.name in replacements:
            continue
        new.addfile(entry, old.extractfile(entry) if entry.isfile() else None)
    for name, data in [('runtime.json', json.dumps(metadata).encode()),
                       ('sources/BrowserFrontend.lean', frontend.encode())]:
        entry = tarfile.TarInfo(name)
        entry.size = len(data)
        new.addfile(entry, io.BytesIO(data))
    for name, file in replacements.items():
        new.add(file, arcname=name)
digest = hashlib.file_digest(args.output.open('rb'), 'sha256').hexdigest()
args.config.write_text(json.dumps({**pin, 'file': str(args.output.resolve()),
    'sha256': digest, 'bytes': args.output.stat().st_size, 'ampleCommit': metadata['ampleCommit']}, indent=2) + '\n')
print('Prepared development browser runtime:', args.output, digest)
