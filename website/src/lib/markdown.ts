import { Marked } from 'marked';
import markedKatex from 'marked-katex-extension';

// A dedicated parser avoids registering extensions repeatedly during dev reloads.
// Render at build time, including MathML for assistive technology.
const markdown = new Marked(markedKatex({
  throwOnError: true,
  trust: false,
  output: 'htmlAndMathml',
}));

export function renderMarkdown(source: string): string {
  return markdown.parse(source, { async: false });
}
