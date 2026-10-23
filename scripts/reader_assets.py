"""Publish each reader build at immutable, content-addressed asset URLs."""
import hashlib
from pathlib import Path
import re
import shutil


THEME_CONTROL = '''<label class="book-theme-control" hidden>
<svg viewBox="0 0 20 20" fill="none" aria-hidden="true"><circle cx="10" cy="10" r="7" stroke="currentColor" stroke-width="1.4"/><path d="M10 3a7 7 0 0 1 0 14Z" fill="currentColor"/></svg>
<select data-book-theme aria-label="테마" title="테마">
<option value="system">자동</option><option value="light">라이트</option><option value="dark">다크</option>
</select></label>'''


def prepare_theme(html: str):
    # Redirect-only pages have no reader chrome or shared asset base. Attaching
    # book-relative assets there would request them under the obsolete path.
    if '</header>' not in html:
        return html
    # Resolve <base> first, then run the tiny blocking bootstrap before CSS.
    # Verso's order of extra assets is not a first-paint ordering guarantee.
    html = re.sub(r'<script\b[^>]*\bsrc="-verso-data/theme\.js"[^>]*></script>\s*', '', html)
    html = re.sub(r'<link\b[^>]*\bhref="-verso-data/theme\.css"[^>]*>\s*', '', html)
    bootstrap = '<meta name="color-scheme" content="light dark"><script src="-verso-data/theme.js"></script>'
    html, count = re.subn(r'(<meta charset="utf-8">)', lambda m: m[0] + bootstrap, html, count=1)
    if count != 1:
        raise ValueError('A reading page must declare UTF-8 before the theme bootstrap')
    html = html.replace('</head>', '<link rel="stylesheet" href="-verso-data/theme.css"></head>', 1)
    return html.replace('</header>', THEME_CONTROL + '</header>', 1)


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
