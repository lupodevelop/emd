import { readFileSync } from 'node:fs';
import type { APIRoute } from 'astro';

// Emit the repository's current PDF as a static asset on every site build.
export const GET: APIRoute = () => new Response(
  new Uint8Array(readFileSync(`${process.cwd()}/../paper/emd.pdf`)),
  { headers: {
    'Content-Type': 'application/pdf',
    'Content-Disposition': 'inline; filename="emd.pdf"',
  } },
);
