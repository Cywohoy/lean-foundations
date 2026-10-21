"""Package matching browser artifacts into compressed, independently checked packs."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('--lean-lib', type=Path, required=True)
parser.add_argument('--ample-lib', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
output = args.output.resolve()
roots = [args.lean_lib.resolve(), args.ample_lib.resolve()]
assert all(output != root and root not in output.parents for root in roots), 'Keep packs separate from the library'
output.mkdir(parents=True, exist_ok=True)
sources = {}
for root in roots:
    for file in root.rglob('*'):
        name = file.relative_to(root).as_posix()
        if file.is_file() and name.endswith(('.olean', '.ir', '.ir.sig')) and not name.startswith('Tests/'):
            sources[name] = file
packs = []
for layer in ['init', 'rest']:
    parts = []
    entries = []
    size = 0

    def flush():
        global parts, entries, size
        if not entries:
            return
        raw = b''.join(parts)
        compressed = gzip.compress(raw, compresslevel=5, mtime=0)
        filename = f'{layer}-{len(packs):03}.pack'
        (output / filename).write_bytes(compressed)
        packs.append({'file': filename, 'layer': layer, 'rawBytes': len(raw),
            'bytes': len(compressed), 'sha256': hashlib.sha256(compressed).hexdigest(), 'entries': entries})
        parts, entries, size = [], [], 0

    for name, source in sorted(sources.items()):
        is_init = name == 'Init.olean' or name.startswith('Init/')
        if is_init != (layer == 'init'):
            continue
        data = source.read_bytes()
        if size and size + len(data) > 16 * 1024 * 1024:
            flush()
        entries.append({'path': name, 'offset': size, 'bytes': len(data)})
        parts.append(data)
        size += len(data)
    flush()
manifest = {'schemaVersion': 1, 'files': sorted(sources), 'packs': packs}
(output / 'library.json').write_text(json.dumps(manifest, separators=(',', ':')) + '\n', encoding='utf-8')
print(f'{len(sources)} files, {len(packs)} packs, {sum(pack["rawBytes"] for pack in packs)} raw bytes, '
      f'{sum(pack["bytes"] for pack in packs)} gzip bytes')
