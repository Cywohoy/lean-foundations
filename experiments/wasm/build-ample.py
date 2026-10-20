"""Compile Ample with the matching native 32-bit compiler into an isolated tree.

Only source files are read from Ample. Its normal Lake build and toolchain are
not modified. The resulting olean files contain interpreter code for its tactics.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument('--lean', type=Path, required=True)
parser.add_argument('--lean-lib', type=Path, required=True)
parser.add_argument('--ample', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
parser.add_argument('--module', action='append', help='Build only these roots (default: all public modules)')
args = parser.parse_args()
lean = args.lean.resolve()
with lean.open('rb') as compiler_file:
    elf_header = compiler_file.read(5)
assert elf_header == b'\x7fELF\x01', 'Use the matching native 32-bit ELF compiler, not the normal desktop toolchain'
library = args.lean_lib.resolve()
ample = args.ample.resolve()
output = args.output.resolve()
assert output != ample and ample not in output.parents, 'Use an output folder outside the source checkout'
output.mkdir(parents=True, exist_ok=True)
env = os.environ.copy()
env['LEAN_PATH'] = os.pathsep.join(map(str, [output, library]))
sources = {'Ample': ample / 'Ample.lean'}
sources.update({'.'.join(path.relative_to(ample).with_suffix('').parts): path
                for path in (ample / 'Ample').rglob('*.lean')})
imports = {}
for name, path in sources.items():
    text = path.read_text(encoding='utf-8')
    imports[name] = [match[1] for match in re.finditer(
        r'^(?:(?:public|meta)\s+)*import\s+(Ample(?:\.[A-Za-z0-9_]+)*)\s*$', text, re.M)]

ordered = []
visiting = set()
visited = set()


def visit(name):
    if name in visited:
        return
    assert name not in visiting, f'Import cycle at {name}'
    assert name in sources, f'Missing Ample module {name}'
    visiting.add(name)
    for dependency in imports[name]:
        visit(dependency)
    visiting.remove(name)
    visited.add(name)
    ordered.append(name)


for root in args.module or sorted(sources):
    visit(root)
version = subprocess.run([str(lean), '--version'], capture_output=True, text=True, check=True).stdout.strip()
assert '4.35.0' in version, version
record = {'compiler': version, 'wordBits': 32, 'modules': []}
for index, name in enumerate(ordered, 1):
    source = sources[name]
    target = output / Path(*name.split('.')).with_suffix('.olean')
    target.parent.mkdir(parents=True, exist_ok=True)
    print(f'[{index}/{len(ordered)}] {name}', flush=True)
    subprocess.run([str(lean), '-o', str(target), str(source)], cwd=ample, env=env, check=True)
    record['modules'].append({'name': name,
        'sourceSha256': hashlib.sha256(source.read_bytes()).hexdigest(),
        'oleanSha256': hashlib.sha256(target.read_bytes()).hexdigest()})
(output / 'ample-build.json').write_text(json.dumps(record, indent=2) + '\n', encoding='utf-8')
