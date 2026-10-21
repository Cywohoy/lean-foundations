"""Render the reader's navigation before the browser paints the first frame."""
from html import escape
from html.parser import HTMLParser
import re
from urllib.parse import parse_qs, urlsplit, urlunsplit


class Label(HTMLParser):
    def __init__(self):
        super().__init__()
        self.parts = []
        self.skip = 0

    def handle_starttag(self, tag, attrs):
        if self.skip:
            self.skip += 1
        elif 'permalink-widget' in dict(attrs).get('class', '').split():
            self.skip = 1

    def handle_endtag(self, tag):
        if self.skip:
            self.skip -= 1

    def handle_data(self, text):
        if not self.skip:
            self.parts.append(text)


def label(source):
    parser = Label()
    parser.feed(source)
    return ''.join(parser.parts).strip()


class Attributes(HTMLParser):
    def __init__(self, source):
        super().__init__()
        self.tags = []
        self.feed(source)

    def handle_starttag(self, tag, attrs):
        self.tags.append((tag, dict(attrs)))


def render_navigation(html):
    start = re.search(r'<div\s+class="split-tocs">', html)
    if not start:
        return html
    depth = 0
    end = None
    for tag in re.finditer(r'</?div\b[^>]*>', html[start.start():]):
        depth += -1 if tag.group().startswith('</') else 1
        if depth == 0:
            end = start.start() + tag.end()
            break
    if end is None:
        raise ValueError('Unclosed navigation container')
    old = html[start.start():end]
    book = re.search(r'<div class="split-toc book">.*?<table>(.*?)</table>', old, re.S)
    if not book:
        raise ValueError('Missing book navigation table')

    sections = []
    for heading in re.finditer(r'<h2\b[^>]*>.*?</h2>', html, re.S):
        tags = Attributes(heading.group()).tags
        attrs = next(attrs for tag, attrs in tags if tag == 'h2')
        section_id = attrs.get('id')
        if not section_id:
            for tag, attrs in tags:
                if tag == 'a':
                    section_id = parse_qs(urlsplit(attrs.get('href', '')).query).get('name', [None])[0]
                    if section_id:
                        break
        if section_id:
            sections.append((section_id, label(heading.group())))

    items = []
    for row in re.finditer(r'<tr\b([^>]*)>(.*?)</tr>', book.group(1), re.S):
        attrs = Attributes('<tr' + row.group(1) + '>').tags[0][1]
        link = re.search(r'<a\b[^>]*>(.*?)</a>', row.group(2), re.S)
        if not link:
            continue
        target = Attributes(link.group()).tags[0][1]['href']
        number = re.search(r'<td class="num">([^<]*)', row.group(2))
        text = ((label(number.group(1)) + ' ') if number and number.group(1).strip() else '') + label(link.group(1))
        current = 'current' in attrs.get('class', '').split()
        selected = ' aria-current="page"' if current else ''
        item = f'<li><a class="book-chapter-link" href="{escape(target, quote=True)}"{selected}>{escape(text)}</a>'
        if current and sections:
            parts = urlsplit(target)
            children = ''.join(
                '<li><a href="' + escape(urlunsplit(parts._replace(fragment=section_id)), quote=True) + '">'
                + escape(text) + '</a></li>' for section_id, text in sections)
            item += '<ol>' + children + '</ol>'
        items.append(item + '</li>')
    tree = '<ol class="book-toc-tree" aria-label="목차">' + ''.join(items) + '</ol>'
    return html[:start.start()] + tree + html[end:]
