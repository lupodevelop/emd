import assert from 'node:assert/strict';
import test from 'node:test';
import { defaultTitle, defaultDescription, jsonLd, pageMetadata, publicationDate } from '../src/lib/metadata.ts';

const defaults = {
  root: new URL('https://example.org/emd/'), pathname: '/emd/',
  title: defaultTitle, description: defaultDescription, kind: 'home',
};

test('canonical URLs use the configured origin and omit tracking parameters', () => {
  const meta = pageMetadata({ ...defaults, pathname: '/emd/keyboard/?utm_source=linkedin#run', kind: 'keyboard' });
  assert.equal(meta.canonical, 'https://example.org/emd/keyboard/');
  assert.equal(meta.image, 'https://example.org/emd/social/keyboard.png');
});

test('a different deployment base is respected by graph links and preview images', () => {
  const meta = pageMetadata({ ...defaults, root: new URL('https://example.org/research/dashes/'),
    pathname: '/research/dashes/', kind: 'home' });
  assert.equal(meta.image, 'https://example.org/research/dashes/social/home.png');
  const graph = JSON.parse(meta.structuredData)['@graph'];
  assert.equal(graph.find(node => node['@type'] === 'WebSite').url, 'https://example.org/research/dashes/');
});

test('manual articles have breadcrumbs through the manual index', () => {
  const meta = pageMetadata({ ...defaults, pathname: '/emd/docs/assembly/', kind: 'manual' });
  const graph = JSON.parse(meta.structuredData)['@graph'];
  assert.ok(graph.some(node => node['@type'] === 'TechArticle'));
  assert.deepEqual(graph.find(node => node['@type'] === 'BreadcrumbList').itemListElement.map(item => item.item),
    ['https://example.org/emd/', 'https://example.org/emd/docs/', 'https://example.org/emd/docs/assembly/']);
});

test('paper metadata comes from the manuscript and does not claim a journal or DOI', () => {
  const paper = { title: 'A research paper', author: 'The author', orcid: '0009-0008-3931-8821', date: 'November 5, 2026', abstractText: 'Proofs concern models; implementation checks have finite bounds.' };
  const meta = pageMetadata({ ...defaults, pathname: '/emd/paper/', kind: 'paper', paper });
  const graph = JSON.parse(meta.structuredData)['@graph'];
  const article = graph.find(node => node['@type'] === 'ScholarlyArticle');
  assert.equal(article.headline, paper.title);
  assert.equal(article.abstract, paper.abstractText);
  assert.equal(article.creativeWorkStatus, 'Preprint');
  assert.equal(article.datePublished, '2026-11-05');
  assert.equal(article.encoding.contentUrl, 'https://example.org/emd/paper/emd.pdf');
  assert.equal(graph.find(node => node['@type'] === 'Person').name, paper.author);
  assert.ok(!('identifier' in article));
  assert.ok(!('publisher' in article));
});

test('JSON-LD containing markup cannot close its script element', () => {
  const hostile = '</script><img src=x onerror=alert(1)>\u2028\u2029';
  const serialized = jsonLd({ name: hostile });
  assert.ok(!serialized.includes('<'));
  assert.ok(!serialized.includes('\u2028'));
  assert.deepEqual(JSON.parse(serialized), { name: hostile });
});

test('paper dates reject invalid or ambiguous values', () => {
  assert.equal(publicationDate('February 29, 2024'), '2024-02-29');
  for (const value of ['February 29, 2026', 'November 31, 2026', 'yesterday', '05/11/2026']) {
    assert.throws(() => publicationDate(value));
  }
});
