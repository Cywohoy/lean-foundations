"""Package the tested toolchain for static Pages hosting; never add binaries to Git."""
import argparse
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tarfile
import tempfile
import re

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument('--toolchain', type=Path, required=True, help='The matching stage1 directory')
parser.add_argument('--ample-lib', type=Path, required=True)
parser.add_argument('--upstream', type=Path, default=ROOT / 'tmp/wasm/upstream')
parser.add_argument('--coi', type=Path, default=ROOT / 'tmp/wasm/coi-serviceworker')
parser.add_argument('--output', type=Path, required=True)
parser.add_argument('--contexts', type=Path, help='Checked wasm32 chapters and exercise prefixes from build_browser_book.py')
parser.add_argument('--reuse-library', type=Path,
                    help='Reuse packs after host/linker-only changes; never after Lean source changes')
args = parser.parse_args()
toolchain = args.toolchain.resolve()
source = toolchain.parents[2]
ample = ROOT.parent / 'Ample'
revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ample, text=True).strip()
if subprocess.check_output(['git', 'status', '--porcelain'], cwd=ample, text=True).strip():
    raise SystemExit('Commit the matching Ample source before packaging a public runtime')
if 'ample-dlsym-lazy-index' not in (toolchain / 'bin/lean.js').read_text():
    raise SystemExit('Run optimize-runtime.py and runtime-tests.cjs before packaging')
args.output.parent.mkdir(parents=True, exist_ok=True)
(ROOT / 'tmp').mkdir(parents=True, exist_ok=True)
with tempfile.TemporaryDirectory(prefix='browser-bundle-', dir=ROOT / 'tmp') as temporary:
    packs = Path(temporary)
    if args.reuse_library:
        with tarfile.open(args.reuse_library) as previous:
            old = json.load(previous.extractfile('runtime.json'))
            current = json.loads((args.ample_lib / 'ample-build.json').read_text())
            if old['ampleCommit'] != revision or old['ampleBuild'] != current:
                raise SystemExit('The previous bundle uses a different Ample build')
            for member in previous:
                if member.name == 'library.json' or re.fullmatch(r'packs/[a-z0-9-]+\.pack', member.name):
                    if not member.isfile(): raise ValueError('Expected a regular library file')
                    with previous.extractfile(member) as source_file, (packs / Path(member.name).name).open('wb') as output:
                        import shutil
                        shutil.copyfileobj(source_file, output)
    else:
        subprocess.run([sys.executable, str(ROOT / 'experiments/wasm/pack-library.py'),
            '--lean-lib', str(toolchain / 'lib/lean'), '--ample-lib', str(args.ample_lib),
            '--output', str(packs)], check=True)
    files = {f'packs/{p.name}': p for p in packs.glob('*.pack')}
    files.update({
        'library.json': packs / 'library.json',
        'runtime/lean.js': toolchain / 'bin/lean.js',
        'runtime/lean.wasm': toolchain / 'bin/lean.wasm',
        'worker.js': ROOT / 'experiments/wasm/worker.js',
        'upstream-worker.js': args.upstream / 'public/lean-worker-persistent.worker.js',
        'coi-serviceworker.js': args.coi / 'coi-serviceworker.js',
        'licenses/Lean.txt': source / 'LICENSE',
        'licenses/Ample.txt': ample / 'LICENSE',
        'licenses/BrowserWorker.txt': args.upstream / 'LICENSE',
        'licenses/COI.txt': args.coi / 'LICENSE',
        'licenses/Emscripten.txt': source.parent / 'emsdk/upstream/emscripten/LICENSE',
    })
    if args.contexts:
        files['contexts.json'] = args.contexts / 'contexts.json'
        contexts = json.loads(files['contexts.json'].read_text())
        for context in contexts.values():
            for item in context['files']:
                file = args.contexts / item['name']
                if hashlib.sha256(file.read_bytes()).hexdigest() != item['sha256']:
                    raise ValueError('A checked context file changed: ' + str(file))
                files['contexts/' + item['name']] = file
    if (source / 'LICENSES').is_file():
        files['licenses/Lean-dependencies.txt'] = source / 'LICENSES'
    else:
        for file in (source / 'LICENSES').rglob('*'):
            if file.is_file(): files['licenses/Lean-dependencies/' + file.relative_to(source / 'LICENSES').as_posix()] = file
    metadata = {'version': '4.35.0', 'wordBits': 32, 'ampleCommit': revision,
        'leanCommit': 'eb6cafb7290e8bd5f2937522d8d804f58f02bafc',
        'port': json.loads((source / '.ample-wasm-port.json').read_text()),
        'ampleBuild': json.loads((args.ample_lib / 'ample-build.json').read_text())}
    notices = ('Experimental browser Lean 4.35.0 and Ample runtime.\n'
        'Lean and Ample: Apache-2.0; COI Service Worker: MIT; Emscripten: MIT/NCSA.\n'
        'Applicable license texts are retained in licenses/.\n'
        'Sources and reproducible port: https://github.com/Cywohoy/lean-algebra/tree/main/experiments/wasm\n'
        'Ample source: https://github.com/Cywohoy/ample/tree/' + revision + '\n'
        'Worker: cauli/lean4-wasm-in-browser at 017c835ecf0ac8c74745a867c65faeac0baf6654\n'
        'COI: gzuidhof/coi-serviceworker at 7b1d2a092d0d2dd2b7270b6f12f13605de26f214\n')
    with tarfile.open(args.output, 'w:gz', compresslevel=5) as archive:
        for name, data in [('runtime.json', json.dumps(metadata).encode()), ('NOTICE.txt', notices.encode())]:
            entry = tarfile.TarInfo(name); entry.size = len(data); entry.mode = 0o644
            archive.addfile(entry, io.BytesIO(data))
        for name, file in sorted(files.items()):
            entry = archive.gettarinfo(str(file), arcname=name)
            entry.mtime = entry.uid = entry.gid = 0
            entry.uname = entry.gname = ''; entry.mode = 0o644
            with file.open('rb') as stream: archive.addfile(entry, stream)
with args.output.open('rb') as stream:
    digest = hashlib.file_digest(stream, 'sha256').hexdigest()
print(json.dumps({'file': str(args.output), 'sha256': digest, 'bytes': args.output.stat().st_size,
                  'ampleCommit': revision}), flush=True)
