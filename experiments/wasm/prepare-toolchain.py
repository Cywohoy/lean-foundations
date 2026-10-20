"""Apply the pinned browser port without resetting the supplied source checkout."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

BASE = 'eb6cafb7290e8bd5f2937522d8d804f58f02bafc'
HERE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('source', type=Path)
args = parser.parse_args()
source = args.source.resolve()
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=source, text=True).strip()
if head != BASE:
    raise SystemExit(f'Expected Lean 4.35.0 at {BASE}, found {head}')
patch = HERE / 'patches/lean4-4.35.patch'
already_applied = subprocess.run(['git', 'apply', '--reverse', '--check', str(patch)],
                                cwd=source, capture_output=True).returncode == 0
if not already_applied:
    subprocess.run(['git', 'apply', '--check', str(patch)], cwd=source, check=True)
    subprocess.run(['git', 'apply', str(patch)], cwd=source, check=True)
subprocess.run([sys.executable, str(HERE / 'install-frontend.py'), str(source)], check=True)
shutil.copyfile(HERE / 'generate-exports.py', source / 'script/generate-wasm-exports.py')
record = {'baseCommit': BASE, 'inputs': {name: hashlib.sha256((HERE / name).read_bytes()).hexdigest()
    for name in ['patches/lean4-4.35.patch', 'Frontend.lean', 'install-frontend.py',
                 'generate-exports.py', 'optimize-runtime.py', 'runtime-tests.cjs', 'build-toolchain.sh']}}
record['inputs']['worker.js'] = hashlib.sha256((HERE / 'worker.js').read_bytes()).hexdigest()
(source / '.ample-wasm-port.json').write_text(json.dumps(record, indent=2) + '\n', encoding='utf-8')
print(f'Prepared isolated Lean browser source: {source}')
