import type { APIRoute } from 'astro';
import { exampleFile, examplePaths } from '../../lib/example-files';

export const getStaticPaths = examplePaths;
export const GET: APIRoute = ({ params }) => exampleFile(params.name, 'emd');
