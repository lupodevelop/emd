import type { APIRoute } from 'astro';
import { manuals } from '../lib/site';

export const GET: APIRoute = ({ site }) => {
  if (!site) throw new Error('Sitemap requires site in astro.config.mjs');
  const root = new URL(import.meta.env.BASE_URL, site);
  const paths = ['', 'keyboard/', 'docs/', 'paper/', 'paper/2/', ...manuals.map(page => `docs/${page.slug}/`)];
  const escape = (text: string) => text.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/"/g, '&quot;');
  return new Response(`<?xml version="1.0" encoding="UTF-8"?>\n<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">\n${paths.map(path => `  <url><loc>${escape(new URL(path, root).href)}</loc></url>`).join('\n')}\n</urlset>\n`,
    { headers: { 'Content-Type': 'application/xml; charset=utf-8' } });
};
