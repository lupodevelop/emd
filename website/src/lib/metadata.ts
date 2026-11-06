import cards from './social-cards.json' with { type: 'json' };

export const defaultTitle = 'emd — a programming language made of Unicode dashes';
export const defaultDescription = 'emd is a programming language written in eight Unicode dashes, with 32 instructions, a Rust compiler and VM, a browser playground, and semantics formalized in Lean and Rocq.';
export const repository = 'https://github.com/lupodevelop/emd';
export const author = { name: 'Daniele Scaratti', orcid: '0009-0008-3931-8821' };

export type PageKind = keyof typeof cards;
export type PaperMetadata = { title: string; author: string; orcid: string; date: string; doi?: string; abstractText?: string; pdfPath?: string; keywords?: string[] };

// Parse the publication date from the paper metadata.
export function publicationDate(date: string): string {
  const months = ['January', 'February', 'March', 'April', 'May', 'June',
    'July', 'August', 'September', 'October', 'November', 'December'];
  const match = /^(\w+) (\d{1,2}), (\d{4})$/.exec(date);
  const month = match ? months.indexOf(match[1]) + 1 : 0;
  if (!match || !month) throw new Error(`Unsupported manuscript date: ${date}`);
  const iso = `${match[3]}-${String(month).padStart(2, '0')}-${match[2].padStart(2, '0')}`;
  if (new Date(iso).toISOString().slice(0, 10) !== iso) throw new Error(`Invalid manuscript date: ${date}`);
  return iso;
}

// Inline JSON must not be able to close its surrounding script element.
export function jsonLd(data: unknown): string {
  return JSON.stringify(data).replace(/</g, '\\u003c').replace(/\u2028/g, '\\u2028').replace(/\u2029/g, '\\u2029');
}

export function pageMetadata({ root, pathname, title, description, kind, paper }: {
  root: URL; pathname: string; title: string; description: string; kind: PageKind; paper?: PaperMetadata;
}) {
  const canonical = new URL(pathname, root);
  canonical.search = '';
  canonical.hash = '';
  const absolute = (path: string) => new URL(path, root).href;
  const image = absolute(`social/${kind}.png`);
  const person = {
    '@type': 'Person', '@id': `https://orcid.org/${paper?.orcid ?? author.orcid}`,
    name: paper?.author ?? author.name, sameAs: ['https://github.com/lupodevelop'],
  };
  const ref = (id: string) => ({ '@id': id });
  const language = {
    '@type': 'ComputerLanguage', '@id': absolute('#language'), name: 'emd',
    alternateName: ['em dash', 'Emotional damage'], url: root.href,
    description: 'An esoteric stack-based programming language written entirely in eight Unicode dashes.',
  };
  const software = {
    '@type': 'SoftwareSourceCode', '@id': absolute('#software'), name: 'emd',
    description: 'The Rust implementation of emd: assembler, virtual machine, static analyzer, debugger and WebAssembly playground.',
    url: root.href, codeRepository: repository, programmingLanguage: 'Rust',
    license: 'https://spdx.org/licenses/MIT.html', author: ref(person['@id']),
    about: ref(language['@id']),
  };
  const website = {
    '@type': 'WebSite', '@id': absolute('#website'), url: root.href,
    name: 'emd — emotional damage', description: defaultDescription, inLanguage: 'en',
    author: ref(person['@id']), about: ref(language['@id']),
  };
  const isManualArticle = kind === 'manual' && canonical.href !== absolute('docs/');
  const page = {
    '@type': isManualArticle ? 'TechArticle' : 'WebPage', '@id': `${canonical.href}#webpage`,
    url: canonical.href, name: title, headline: title, description, inLanguage: 'en',
    isPartOf: ref(website['@id']), about: ref(language['@id']), author: ref(person['@id']),
    image, ...(kind === 'home' ? { mainEntity: ref(software['@id']) } : {}),
  };
  const graph: Record<string, unknown>[] = [website, person, language, software, page];
  if (canonical.href !== root.href) {
    const crumbs = [{ name: 'emd', item: root.href }];
    if (isManualArticle) crumbs.push({ name: 'Manual', item: absolute('docs/') });
    crumbs.push({ name: title.replace(/ — emd$/, ''), item: canonical.href });
    const breadcrumb = {
      '@type': 'BreadcrumbList', '@id': `${canonical.href}#breadcrumbs`,
      itemListElement: crumbs.map((crumb, i) => ({ '@type': 'ListItem', position: i + 1, ...crumb })),
    };
    graph.push(breadcrumb);
    Object.assign(page, { breadcrumb: ref(breadcrumb['@id']) });
  }
  if (paper) {
    const article = {
      '@type': 'ScholarlyArticle', '@id': `${canonical.href}#article`,
      name: paper.title, headline: paper.title, description,
      creativeWorkStatus: 'Preprint',
      ...(paper.doi ? { identifier: { '@type': 'PropertyValue', propertyID: 'DOI', value: paper.doi }, sameAs: `https://doi.org/${paper.doi}` } : {}),
      ...(paper.abstractText ? { abstract: paper.abstractText } : {}),
      keywords: paper.keywords ?? ['programming languages', 'formal semantics', 'Lean', 'Rocq', 'compiler verification', 'bounded model checking'],
      url: canonical.href, image, inLanguage: 'en',
      author: ref(person['@id']), datePublished: publicationDate(paper.date),
      mainEntityOfPage: ref(page['@id']), about: ref(language['@id']),
      encoding: { '@type': 'MediaObject', contentUrl: absolute(paper.pdfPath ?? 'paper/emd.pdf'), encodingFormat: 'application/pdf' },
    };
    graph.push(article);
    Object.assign(page, { mainEntity: ref(article['@id']) });
  }
  return { canonical: canonical.href, image, imageAlt: cards[kind].alt,
    author: person.name, ogType: paper ? 'article' : 'website',
    structuredData: jsonLd({ '@context': 'https://schema.org', '@graph': graph }) };
}
