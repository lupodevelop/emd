#!/usr/bin/env python3
"""Validate the metadata crawlers actually receive, on every built HTML page."""
import argparse
import json
import struct
import sys
import xml.etree.ElementTree as ET
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import urlsplit


class Head(HTMLParser):
    def __init__(self):
        super().__init__()
        self.meta = {}
        self.links = {}
        self.jsonld = []
        self.capture = False
        self.script = ''

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if tag == 'meta':
            name = attrs.get('property', attrs.get('name'))
            if name:
                self.meta.setdefault(name, []).append(attrs.get('content', ''))
        if tag == 'link':
            self.links.setdefault(attrs.get('rel'), []).append(attrs)
        if tag == 'script' and attrs.get('type') == 'application/ld+json':
            self.capture = True
            self.script = ''

    def handle_data(self, data):
        if self.capture:
            self.script += data

    def handle_endtag(self, tag):
        if tag == 'script' and self.capture:
            self.jsonld.append(json.loads(self.script))
            self.capture = False


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--dist', type=Path, default=Path(__file__).resolve().parents[1] / 'dist')
    ap.add_argument('--site', default='https://lupodevelop.github.io')
    ap.add_argument('--base', default='/emd/')
    args = ap.parse_args()
    errors = []

    def check(condition, message):
        if not condition:
            errors.append(message)

    root = args.site.rstrip('/') + '/' + args.base.strip('/') + '/'
    pages = sorted(args.dist.rglob('index.html'))
    check(bool(pages), 'No built pages found')
    canonical_urls = set()
    descriptions = set()
    for file in pages:
        route = file.parent.relative_to(args.dist).as_posix()
        route = '' if route == '.' else route + '/'
        expected = root + route
        head = Head()
        head.feed(file.read_text())
        label = route or 'home'

        def meta(name):
            values = head.meta.get(name, [])
            check(len(values) == 1 and bool(values[0]), f'{label}: missing/duplicate {name}')
            return values[0] if values else ''

        canonicals = head.links.get('canonical', [])
        check(len(canonicals) == 1 and canonicals[0].get('href') == expected,
              f'{label}: canonical must be {expected}')
        check(meta('og:url') == expected, f'{label}: og:url differs from canonical')
        if 'noindex' not in head.meta.get('robots', [''])[0].split(', '):
            canonical_urls.add(expected)
        description = meta('description')
        check(description not in descriptions, f'{label}: duplicate page description')
        descriptions.add(description)
        check(meta('og:description') == description, f'{label}: OG description differs')
        check(meta('twitter:description') == description, f'{label}: X description differs')
        check(meta('og:title') == meta('twitter:title'), f'{label}: social titles differ')
        check(meta('twitter:card') == 'summary_large_image', f'{label}: missing large card')
        for name in ['og:site_name', 'og:type', 'og:locale', 'og:image:alt', 'author', 'robots']:
            meta(name)
        image = meta('og:image')
        check(image.startswith(root), f'{label}: preview image must be an absolute site URL')
        check(meta('twitter:image') == image, f'{label}: preview images differ')
        check(meta('twitter:image:alt') == meta('og:image:alt'), f'{label}: preview alt text differs')
        check(meta('og:image:width') == '1200' and meta('og:image:height') == '630',
              f'{label}: preview dimensions')
        if image.startswith(root):
            asset = args.dist / image[len(root):]
            check(asset.is_file(), f'{label}: preview image is missing')
            if asset.is_file():
                data = asset.read_bytes()
                check(data[:8] == b'\x89PNG\r\n\x1a\n', f'{label}: preview is not PNG')
                check(len(data) >= 24 and struct.unpack('>II', data[16:24]) == (1200, 630),
                      f'{label}: actual PNG dimensions')
        check(len(head.jsonld) == 1, f'{label}: expected one JSON-LD graph')
        if head.jsonld:
            graph = head.jsonld[0]
            check(graph.get('@context') == 'https://schema.org', f'{label}: schema context')
            nodes = graph.get('@graph', [])
            check(any(n.get('@type') == 'WebSite' for n in nodes), f'{label}: missing WebSite')
            page = next((n for n in nodes if n.get('@id') == expected + '#webpage'), {})
            check(page.get('url') == expected, f'{label}: structured page URL')
            breadcrumbs = next((n for n in nodes if n.get('@type') == 'BreadcrumbList'), None)
            check(not route or breadcrumbs is not None, f'{label}: missing breadcrumbs')
            if breadcrumbs:
                check(breadcrumbs['itemListElement'][-1]['item'] == expected,
                      f'{label}: breadcrumb does not end at page')
            papers = {'paper/': 'paper/emd.pdf', 'paper/2/': 'paper/2/experiment.pdf'}
            if route in papers:
                article = next((n for n in nodes if n.get('@type') == 'ScholarlyArticle'), {})
                check(bool(article), 'paper: missing ScholarlyArticle')
                check(meta('og:type') == 'article', 'paper: OG type')
                check(meta('citation_title') == article.get('headline'), 'paper: citation title')
                check(meta('citation_publication_date') == article.get('datePublished'), 'paper: citation date')
                check(meta('citation_pdf_url') == root + papers[route], 'paper: citation PDF URL')
                check(bool(meta('citation_author')), 'paper: citation author')
                data_file = 'experiment.json' if route == 'paper/2/' else 'paper.json'
                manuscript = json.loads((Path(__file__).resolve().parents[1] / 'src/data' / data_file).read_text())
                doi = manuscript.get('doi')
                if doi:
                    check(meta('citation_doi') == doi, 'paper: citation DOI differs from manuscript')
                    check(article.get('identifier') == {
                        '@type': 'PropertyValue', 'propertyID': 'DOI', 'value': doi,
                    }, 'paper: structured DOI differs from manuscript')
                    check(article.get('sameAs') == f'https://doi.org/{doi}', 'paper: DOI link differs from manuscript')
                else:
                    check('citation_doi' not in head.meta and 'identifier' not in article,
                          'paper: DOI supplied without manuscript metadata')

    sitemap = args.dist / 'sitemap.xml'
    check(sitemap.is_file(), 'Missing sitemap.xml')
    if sitemap.is_file():
        xml = ET.fromstring(sitemap.read_text())
        locations = [e.text for e in xml.findall('{*}url/{*}loc')]
        check(set(locations) == canonical_urls and len(locations) == len(canonical_urls),
              'Sitemap must list every indexable HTML page exactly once, without assets')
    robots = args.dist / 'robots.txt'
    check(robots.is_file(), 'Missing robots.txt')
    if robots.is_file():
        check('Sitemap: ' + root + 'sitemap.xml' in robots.read_text(), 'Robots sitemap URL')
    if errors:
        print('\n'.join('FAIL ' + e for e in errors), file=sys.stderr)
        return 1
    print(f'Metadata verified: {len(pages)} pages, canonical URLs, social cards, JSON-LD, citations, sitemap and robots.')
    return 0


if __name__ == '__main__':
    sys.exit(main())
