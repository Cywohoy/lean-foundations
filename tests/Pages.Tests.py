"""Check the static book under a repository URL prefix, as used by GitHub Pages."""
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import unquote, urljoin, urlsplit

root = Path(__file__).resolve().parents[1]
site = root / '_out/pages'
book = site / 'foundations'
prefix = '/lean-foundations/'
origin = 'https://example.test'


class Links(HTMLParser):
    def __init__(self):
        super().__init__()
        self.base = None
        self.urls = []
        self.static = False

    def handle_starttag(self, tag, pairs):
        attrs = dict(pairs)
        if tag == 'base':
            self.base = attrs.get('href')
            return
        if tag == 'meta' and attrs.get('name') == 'book-mode':
            self.static = attrs.get('content') == 'wasm'
        for key in ('href', 'src'):
            if attrs.get(key): self.urls.append(attrs[key])
        if tag == 'meta' and attrs.get('http-equiv', '').lower() == 'refresh':
            self.urls.append(attrs['content'].split('url=', 1)[1])


pages = list(site.rglob('*.html'))
assert pages, 'Stage the site first: python scripts/prepare_pages.py'
checked = 0
for page in pages:
    parser = Links()
    parser.feed(page.read_text(encoding='utf-8'))
    if page.is_relative_to(book):
        assert parser.static, page
    url = origin + prefix + page.relative_to(site).as_posix()
    base = urljoin(url, parser.base) if parser.base else url
    for link in parser.urls:
        target = urlsplit(urljoin(base, link))
        if target.scheme not in ('http', 'https') or target.netloc != 'example.test':
            continue
        assert target.path.startswith(prefix), (page, link, target.path)
        local = site / unquote(target.path[len(prefix):])
        if local.is_dir(): local /= 'index.html'
        assert local.is_file(), (page, link, local)
        checked += 1

assert (site / '.nojekyll').is_file()
if 'content="wasm"' in (book / 'index.html').read_text(encoding='utf-8'):
    import json
    import re
    runtime_path = re.search(r'<meta name="lean-wasm-base" content="([^"]+)">',
                             (book / 'index.html').read_text(encoding='utf-8')).group(1)
    runtime = book / runtime_path
    assert runtime.parent == book / 'wasm'
    metadata = json.loads((runtime / 'runtime.json').read_text())
    assert metadata['version'] == '4.35.0'
    assert len(metadata['ampleCommit']) == 40
    assert (runtime / 'runtime/lean.wasm').is_file()
    assert (runtime / 'library.json').is_file()
    assert (runtime / 'licenses/Lean.txt').is_file()
    assert (book / 'coi-serviceworker.js').is_file()
    assert (book / 'assets/web/wasm-reader.js').is_file()
    assert (book / 'assets/web/exercise-model.js').is_file()
    assert not any('AlgebraBook.' in item['before'] for item in json.loads((book / 'playground.json').read_text()).values())
    assert all(item.get('contextFiles') for item in json.loads(
        (book / 'playground.json').read_text(encoding='utf-8')).values() if item.get('exercise'))
assert not (site / 'operations-and-groups').exists()
# Reading does not require opening another page for each small subsection.
reading_pages = [p for p in book.rglob('index.html')
                 if p.relative_to(book).as_posix() not in ('find/index.html', 'search/index.html')
                 and '<main>' in p.read_text(encoding='utf-8')]
assert len(reading_pages) == 7, reading_pages  # cover, four chapters, two appendices
for page in reading_pages:
    html = page.read_text(encoding='utf-8')
    assert html.count('<ol class="book-toc-tree"') == 1, page
    assert 'class="split-tocs"' not in html, page
    for name in ('NanumSquareNeo-ExtraBold.woff2', 'PretendardVariable.woff2', 'CascadiaCode.woff2'):
        preload = f'<link rel="preload" href="-verso-data/{name}" as="font" type="font/woff2" crossorigin>'
        assert preload in html and html.index(preload) < html.index('href="book.css"'), (page, name)
assert all(len(p.relative_to(book).parts) <= 2 for p in reading_pages)
sections = json.loads((book / 'xref.json').read_text(encoding='utf-8'))[
    'Verso.Genre.Manual.section']['contents']
for entries in sections.values():
    for entry in entries:
        address = entry['address'].strip('/')
        page = book / address / 'index.html'
        assert page.is_file(), address
        assert address in ('', 'proof', 'sets-functions', 'numbers-relations', 'sizes', 'tactics', 'symbols'),address
        if len(entry['data']['context']) > 2:
            assert f'id="{entry["id"]}"' in page.read_text(encoding='utf-8'), entry
exercise_items = sorted((v for v in json.loads((book / 'playground.json').read_text(encoding='utf-8')).values()
                         if v.get('exercise')), key=lambda v: v['exerciseOrder'])
assert [v['exerciseOrder'] for v in exercise_items] == list(range(63))
for chapter, count in [('proof', 9), ('sets-functions', 22), ('numbers-relations', 17), ('sizes', 15)]:
    numbers = [v['exerciseNumber'] for v in exercise_items if v['exerciseChapter'] == chapter]
    assert numbers == list(range(1, count + 1)), (chapter, numbers)
progress_index = json.loads((book / 'exercises.json').read_text(encoding='utf-8'))
full_manifest = json.loads((book / 'playground.json').read_text(encoding='utf-8'))
assert len(progress_index) == len(exercise_items)
for key, item in progress_index.items():
    full = full_manifest[key]
    assert item['code'] == full['code']
    assert [f['sha256'] for f in item['contextFiles']] == [f['sha256'] for f in full['contextFiles']]
    assert not {'before', 'sourceBefore'} & item.keys()
    assert all(set(f) == {'sha256'} for f in item['contextFiles'])
print(f'PASS: {len(pages)} static pages and {checked} local links work below {prefix}')
