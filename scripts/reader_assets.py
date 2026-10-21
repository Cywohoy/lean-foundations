"""Publish each reader build at immutable, content-addressed asset URLs."""
import hashlib
from pathlib import Path
import re
import shutil


def stage_reader_assets(book: Path):
    files = [book / 'book.css', *book.glob('*.json')]
    for directory in ('-verso-data', 'assets/web', 'playground'):
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
        if url == 'book.css' or url.startswith(('-verso-data/', 'assets/web/')):
            url = prefix + url
        return attribute + '=' + quote + url + quote
    return re.sub(r'\b(href|src)=([\"\'])([^\"\']+)\2', replace, html)
