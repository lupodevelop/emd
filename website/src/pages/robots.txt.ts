import type { APIRoute } from 'astro';

// A project site serves this at /emd/robots.txt. Crawlers only apply robots rules
// from the origin's /robots.txt; keep that deployment distinction documented.
export const GET: APIRoute = ({ site }) => {
  if (!site) throw new Error('Robots requires site in astro.config.mjs');
  const root = new URL(import.meta.env.BASE_URL, site);
  return new Response(`User-agent: *\nAllow: ${root.pathname}\n\nSitemap: ${new URL('sitemap.xml', root).href}\n`,
    { headers: { 'Content-Type': 'text/plain; charset=utf-8' } });
};
