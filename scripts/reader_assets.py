"""Publish each reader build at immutable, content-addressed asset URLs."""
import hashlib
from pathlib import Path
import re
import shutil


def stage_reader_assets(book: Path):
    files = [*book.glob('*.css'), *book.glob('*.json'), book / 'toc-resize.js']
    for directory in ('-verso-data', '-verso-search', 'assets/web', 'playground'):
        files.extend(p for p in (book / directory).rglob('*') if p.is_file())
    files = sorted(set(files))
    digest = hashlib.sha256()
    for file in files:
        digest.update(file.relative_to(book).as_posix().encode() + b'\0')
        digest.update(file.read_bytes())
    prefix = '_reader/' + digest.hexdigest()[:20] + '/'
    for file in files:
        target = book / prefix / file.relative_to(book)
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(file, target)
    return prefix


def version_reader_links(html: str, prefix: str):
    # Preserve the page base and all reading links. Only asset requests move.
    def replace(match):
        attribute, quote, url = match.groups()
        if url in ('book.css', 'verso-vars.css', 'toc-resize.js') or url.startswith(('-verso-data/', '-verso-search/', 'assets/web/')):
            url = prefix + url
        return attribute + '=' + quote + url + quote
    return re.sub(r'\b(href|src)=([\"\'])([^\"\']+)\2', replace, html)


def prepare_search(book: Path):
    # Verso mounts the input before loading its index, then clears it during
    # registration. Preserve text entered during that network-dependent gap.
    for name in ('search-init.js', 'search-page.js'):
        file = book / '-verso-search' / name
        source = file.read_text(encoding='utf-8')
        assert 'fetch("xref.json")' in source, name
        source = source.replace('fetch("xref.json")',
            'fetch(new URL("xref.json", new URL(document.querySelector(\'meta[name="book-assets-base"]\').content, document.baseURI)))')
        if name == 'search-init.js':
            start = '        registerSearch({'
            end = '            searchPagePath,\n        });'
            assert start in source and end in source, 'Review the updated Verso search registration'
            source = source.replace(start,
                '        const input = searchWrapper.querySelector(\'[role="searchbox"]\');\n'
                '        const pendingQuery = input.textContent;\n' + start)
            source = source.replace(end, end + '\n'
                '        input.dataset.searchReady = "true";\n'
                '        if (pendingQuery) {\n'
                '            input.textContent = pendingQuery;\n'
                '            input.dispatchEvent(new KeyboardEvent("keyup", {key:"Process", bubbles:true}));\n'
                '        }')
        file.write_text(source, encoding='utf-8')
