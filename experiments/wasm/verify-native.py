"""Run Ample's own regressions with the matching 32-bit toolchain and artifacts."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument('--lean', type=Path, required=True)
parser.add_argument('--lean-lib', type=Path, required=True)
parser.add_argument('--ample', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
parser.add_argument('--jobs', type=int, default=2)
args = parser.parse_args()
ample = args.ample.resolve()
output = args.output.resolve()
env = os.environ.copy()
env['LEAN_PATH'] = os.pathsep.join(map(str, [output, args.lean_lib.resolve()]))
for fixture in sorted((ample / 'Tests/Fixtures').rglob('*.lean')):
    target = output / fixture.relative_to(ample).with_suffix('.olean')
    target.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run([str(args.lean), '-o', str(target), str(fixture)], cwd=ample, env=env, check=True)


def verify(source):
    result = subprocess.run([str(args.lean), str(source)], cwd=ample, env=env,
                            capture_output=True, text=True, timeout=180)
    record = {'test': source.name, 'exitCode': result.returncode,
              'stdout': result.stdout, 'stderr': result.stderr}
    print(f'{"PASS" if result.returncode == 0 else "FAIL"}: {source.name}', flush=True)
    if result.returncode:
        print(result.stdout + result.stderr, flush=True)
    return record


with ThreadPoolExecutor(max_workers=args.jobs) as executor:
    results = list(executor.map(verify, sorted((ample / 'Tests').glob('*.lean'))))
(output / 'regressions.json').write_text(json.dumps(results, indent=2) + '\n', encoding='utf-8')
raise SystemExit(any(record['exitCode'] for record in results))
