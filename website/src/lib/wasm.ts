export type EmdExports = {
  memory: WebAssembly.Memory;
  emd_alloc(length: number): number;
  emd_free(at: number, length: number): void;
  emd_run(...args: number[]): number;
  emd_explain(...args: number[]): number;
};

export type RunResult = { ok: boolean; status: string; steps: number; stack: number[]; output: string };
export type Explanation = {
  problems: string[];
  instructions: { index: number; source: string; name: string; effect: string }[];
};

const encoder = new TextEncoder();
const decoder = new TextDecoder();

export function callEmd<T>(wasm: EmdExports, method: 'emd_run' | 'emd_explain', ...texts: string[]): T {
  const buffers: [number, number][] = [];
  try {
    for (const text of texts) {
      const bytes = encoder.encode(text);
      const at = wasm.emd_alloc(bytes.length);
      buffers.push([at, bytes.length]);
      new Uint8Array(wasm.memory.buffer).set(bytes, at);
    }
    const at = wasm[method](...buffers.flat());
    const length = new DataView(wasm.memory.buffer).getUint32(at, true);
    try {
      return JSON.parse(decoder.decode(new Uint8Array(wasm.memory.buffer, at + 4, length)));
    } finally {
      wasm.emd_free(at, length + 4);
    }
  } finally {
    for (const [at, length] of buffers) wasm.emd_free(at, length);
  }
}
