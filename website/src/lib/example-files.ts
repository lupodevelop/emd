import { readFileSync } from 'node:fs';
import { examples } from './examples';

export function examplePaths() {
  return examples.map(example => ({ params: { name: example.name } }));
}

export function exampleFile(name: string | undefined, extension: 'emd' | 'asm') {
  if (!examples.some(example => example.name === name)) return new Response('Not found', { status: 404 });
  return new Response(new Uint8Array(readFileSync(`${process.cwd()}/../examples/${name}.${extension}`)), {
    headers: { 'Content-Type': 'text/plain; charset=utf-8' },
  });
}
