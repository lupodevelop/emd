import publishedPaper from '../data/paper.json' with { type: 'json' };
import { renderToString } from 'katex';

type Paper = {
  title: string;
  author: string;
  orcid: string;
  date: string;
  abstract: string;
  abstractText: string;
  html: string;
  toc: { id: string; title: string }[];
};

function unescapeMath(text: string): string {
  const entities: Record<string, string> = { amp: '&', lt: '<', gt: '>', quot: '"', apos: "'" };
  return text.replace(/&(#x[\da-f]+|#\d+|amp|lt|gt|quot|apos);/gi, (_entity, code: string) => {
    if (code.startsWith('#x')) return String.fromCodePoint(parseInt(code.slice(2), 16));
    if (code.startsWith('#')) return String.fromCodePoint(Number(code.slice(1)));
    return entities[code];
  });
}

// Pandoc keeps the source's math as escaped LaTeX; render it at build time.
export function renderPaperMath(html: string): string {
  return html.replace(/<span class="math (inline|display)">([\s\S]*?)<\/span>/g, (_span, mode, latex) => renderToString(unescapeMath(latex), {
    displayMode: mode === 'display', output: 'htmlAndMathml', trust: false, throwOnError: true,
  }));
}

// Published HTML and PDF are repository assets; a build never needs local manuscript files.
export function loadPaper(paper: Paper = publishedPaper): Paper {
  return { ...paper, abstract: renderPaperMath(paper.abstract), html: renderPaperMath(paper.html) };
}
