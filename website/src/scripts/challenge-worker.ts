import { roomChallenges } from '../lib/room';
import { checkChallenge } from '../lib/challenges';
import { callEmd } from '../lib/wasm';
import type { EmdExports, RunResult } from '../lib/wasm';

self.onmessage = async ({ data }: MessageEvent<{ id: string; source: string; wasmUrl: string; room?: boolean }>) => {
  try {
    const { instance } = await WebAssembly.instantiateStreaming(fetch(data.wasmUrl));
    const wasm = instance.exports as unknown as EmdExports;
    const report = checkChallenge(data.id, data.source,
      (source, input) => callEmd<RunResult>(wasm, 'emd_run', source, input), data.room ? roomChallenges : undefined);
    self.postMessage({ report });
  } catch {
    self.postMessage({ error: 'Could not check the solution. Try again.' });
  }
};
