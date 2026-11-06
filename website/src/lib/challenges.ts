import type { RunResult } from './wasm';

type Case = { name: string; input: string; output: string; stack?: number[] };
export type Challenge = { id: string; title: string; goal: string; hint?: string; cases: Case[] };

export const challenges: Challenge[] = [
  {
    id: 'three', title: 'Leave three',
    goal: 'Halt with exactly [3] on the stack and no output.',
    hint: 'PUSH puts a number on the stack. ADD combines two numbers. End with HALT.',
    cases: [{ name: 'Final stack', input: '', output: '', stack: [3] }],
  },
  {
    id: 'print-a', title: 'Say A',
    goal: 'Print A and halt. No newline or other output.',
    hint: 'WRITE prints one byte. A is byte 65. Build it with arithmetic: literals only go up to 7.',
    cases: [{ name: 'Output', input: '', output: 'A' }],
  },
  {
    id: 'echo', title: 'Echo chamber',
    goal: 'Copy the entire input to the output, then halt. It must also work with empty input.',
    hint: 'READ returns -1 at the end of input. Test for it before WRITE, and loop for the next byte.',
    cases: [
      { name: 'One byte', input: 'A', output: 'A' },
      { name: 'Empty input', input: '', output: '' },
      { name: 'Multiple lines', input: 'emd\nWhy not?\n', output: 'emd\nWhy not?\n' },
      { name: 'Zero byte', input: 'a\0b', output: 'a\0b' },
      { name: 'Unicode', input: 'é—\n', output: 'é—\n' },
    ],
  },
];

export function checkChallenge(id: string, source: string, run: (source: string, input: string) => RunResult, catalog: Challenge[] = challenges) {
  const challenge = catalog.find(item => item.id === id);
  if (!challenge) throw new Error('Unknown challenge');
  const results = challenge.cases.map(test => {
    const actual = run(source, test.input);
    const output = JSON.stringify(actual.output.slice(0, 160)) + (actual.output.length > 160 ? '…' : '');
    const stack = JSON.stringify(actual.stack.slice(0, 8)) + (actual.stack.length > 8 ? '…' : '');
    const stackMatches = !test.stack || (actual.stack.length === test.stack.length
      && actual.stack.every((value, index) => value === test.stack![index]));
    return {
      name: test.name, input: test.input, status: actual.status,
      ok: actual.ok && actual.output === test.output && stackMatches,
      expected: test.stack ? `stack ${JSON.stringify(test.stack)}; output ${JSON.stringify(test.output)}` : JSON.stringify(test.output),
      actual: test.stack ? `stack ${stack}; output ${output}` : output,
    };
  });
  return { passed: results.filter(test => test.ok).length, total: results.length, results };
}

export type ChallengeReport = ReturnType<typeof checkChallenge>;
