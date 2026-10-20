"""Generate a conservative browser interpreter export table from its own build.

Keeping Lean's public C symbols avoids carrying a stale symbol list from an older
compiler. This intentionally favors compatibility over binary size during the
experiment. No C++ internals or undefined symbols are added to the table.
"""
import argparse
from pathlib import Path
import re
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument('--nm', required=True)
parser.add_argument('--output', type=Path, required=True)
parser.add_argument('archives', nargs='+', type=Path)
args = parser.parse_args()
symbols = {'_main', '_malloc', '_free'}
for archive in args.archives:
    result = subprocess.run([args.nm, '--extern-only', '--defined-only', '--format=posix', str(archive)],
                            check=True, capture_output=True, text=True)
    for line in result.stdout.splitlines():
        match = re.match(r'^((?:lean_|l_|(?:runtime_|meta_)?initialize_)[A-Za-z0-9_$]+) [A-Za-z] ', line)
        if match:
            symbols.add('_' + match[1])
args.output.write_text('\n'.join(sorted(symbols)) + '\n', encoding='utf-8')
print(f'Generated {len(symbols)} exports from {len(args.archives)} matching archives')
