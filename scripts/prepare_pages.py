"""Stage the book and its pinned browser Lean runtime for every preview/host."""
import argparse
import json
from pathlib import Path
import shutil

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--wasm-bundle', type=Path)
    parser.add_argument('--runtime-config', type=Path,
                        help='Use a checksum-pinned development runtime without changing the public pin')
    # Accepted for earlier deployment scripts; WASM is now the only output mode.
    parser.add_argument('--download-wasm', action='store_true', help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.runtime_config and not args.wasm_bundle:
        spec = json.loads(args.runtime_config.read_text(encoding='utf-8'))
        if spec.get('file'):
            args.wasm_bundle = ROOT / spec['file']
    output = (ROOT / '_out').resolve()
    assert output.parent == ROOT.resolve(), 'Keep generated output inside this checkout'
    source = (output / 'html-multi').resolve()
    destination = (output / 'pages').resolve()
    # Only replace this script's generated staging folder, never the source or workspace.
    assert destination.parent == output and destination.name == 'pages'
    assert source.parent == output and source != destination
    if not (source / 'index.html').is_file():
        raise SystemExit('Generate the book first: lake exe textbook')
    if destination.exists():
        shutil.rmtree(destination)
    shutil.copytree(source, destination)
    # Keep Verso's existing SRI-verified dependency on the same origin under COEP.
    shutil.copyfile(ROOT / 'assets/web/marked.min.js', destination / '-verso-data/marked.min.js')
    from wasm_pages import prepare
    relative = prepare(destination, args.wasm_bundle, download=not args.wasm_bundle,
                       config=args.runtime_config)
    marker = '<meta name="book-mode" content="wasm">' + f'<meta name="lean-wasm-base" content="{relative}">'
    for page in destination.rglob('*.html'):
        html = page.read_text(encoding='utf-8')
        html = html.replace('https://cdn.jsdelivr.net/npm/marked@11.1.1/marked.min.js', '-verso-data/marked.min.js')
        assert '</head>' in html, page
        page.write_text(html.replace('</head>', marker + '</head>', 1), encoding='utf-8')
    (destination / '.nojekyll').write_text('', encoding='utf-8')
    print('Static book staged in _out/pages.')


if __name__ == '__main__':
    main()
