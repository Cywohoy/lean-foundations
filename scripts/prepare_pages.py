"""Stage the book and its pinned browser Lean runtime for every preview/host."""
import argparse
import json
import os
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
    book = destination / "foundations"
    shutil.copytree(source, book)
    # Keep Verso's existing SRI-verified dependency on the same origin under COEP.
    shutil.copyfile(ROOT / 'assets/web/marked.min.js', book / '-verso-data/marked.min.js')
    from wasm_pages import prepare
    relative = prepare(book, args.wasm_bundle, download=not args.wasm_bundle,
                       config=args.runtime_config)
    marker = '<meta name="book-mode" content="wasm">' + f'<meta name="lean-wasm-base" content="{relative}">'
    from reader_navigation import render_navigation
    for page in book.rglob('*.html'):
        html = page.read_text(encoding='utf-8')
        html = render_navigation(html)
        html = html.replace('https://cdn.jsdelivr.net/npm/marked@11.1.1/marked.min.js', '-verso-data/marked.min.js')
        # Discover the reading fonts before downloading and parsing stylesheets.
        preloads = '\n'.join(
            f'<link rel="preload" href="-verso-data/{font}" as="font" type="font/woff2" crossorigin>'
            for font in ('NanumSquareNeo-ExtraBold.woff2', 'PretendardVariable.woff2', 'CascadiaCode.woff2'))
        html = html.replace('<link rel="stylesheet" href="book.css">',
                            preloads + '\n<link rel="stylesheet" href="book.css">', 1)
        assert '</head>' in html, page
        page.write_text(html.replace('</head>', marker + '</head>', 1), encoding='utf-8')
    shutil.copyfile(ROOT / 'web/portal.html', destination / 'index.html')
    # Keep existing bookmarks, including fragments and query strings. Paths in
    # old redirect pages remain relative to the book after the extra prefix.
    for original in source.rglob('*.html'):
        relative_path = original.relative_to(source)
        if relative_path == Path('index.html'):
            continue
        redirect = destination / relative_path
        if redirect.exists():
            continue
        target = os.path.relpath(book / relative_path, redirect.parent).replace('\\', '/')
        if target.endswith('index.html'):
            target = target[:-10]
        redirect.parent.mkdir(parents=True, exist_ok=True)
        redirect.write_text(
            '<!doctype html><html lang="ko"><head><meta charset="utf-8">'
            '<title>옮겨진 본문</title><script>location.replace('
            + json.dumps(target) + '+location.search+location.hash)</script>'
            + f'<meta http-equiv="refresh" content="0;url={target}">'
            + f'<link rel="canonical" href="{target}"></head>'
            + f'<body><a href="{target}">본문으로 이동</a></body></html>', encoding='utf-8')
    (destination / '.nojekyll').write_text('', encoding='utf-8')
    print('Static book staged in _out/pages.')


if __name__ == '__main__':
    main()
