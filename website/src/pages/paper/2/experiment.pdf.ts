import { readFileSync } from 'node:fs';
import type { APIRoute } from 'astro';

export const GET: APIRoute = () => new Response(
  new Uint8Array(readFileSync(`${process.cwd()}/../benchmarks/llm/report/experiment.pdf`)),
  { headers: {
    'Content-Type': 'application/pdf',
    'Content-Disposition': 'inline; filename="emd-cli-experiment.pdf"',
  } },
);
