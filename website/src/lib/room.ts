import type { Challenge } from './challenges';

const cases = (inputs: string[], transform: (input: string) => string) => inputs.map((input, i) => ({
  name: `Test ${i + 1}`, input, output: transform(input),
}));

export const roomChallenges: Challenge[] = [
  { id: 'room-silence', title: 'Can you do absolutely nothing?',
    goal: 'Halt. Leave the stack empty. Produce no output.',
    cases: [{ name: 'Silence', input: '', output: '', stack: [] }] },
  { id: 'room-answer', title: 'What was the question again?',
    goal: 'Halt with exactly [42] on the stack. Produce no output.',
    cases: [{ name: 'The answer', input: '', output: '', stack: [42] }] },
  { id: 'room-scream', title: 'Can you scream quietly?',
    goal: 'Output exactly A, then halt. No newline.',
    cases: [{ name: 'A small scream', input: '', output: 'A' }] },
  { id: 'room-rescue', title: 'Is anybody receiving this?',
    goal: 'Output exactly SOS, then halt. No spaces or newline.',
    cases: [{ name: 'Distress signal', input: '', output: 'SOS' }] },
  { id: 'room-first', title: 'Can you interrupt a ghost?',
    goal: 'Input contains at least one ASCII byte. Output only its first byte, then halt.',
    cases: cases(['Boo!', '?', '\nNobody here.', ' do not read this', '0123456789'], s => s[0]) },
  { id: 'room-swap', title: 'Which twin arrived first?',
    goal: 'Input is exactly two ASCII bytes. Output them in the opposite order, then halt.',
    cases: cases(['ab', '!?', '00', '\nA', ' z'], s => [...s].reverse().join('')) },
  { id: 'room-count', title: 'How long is a piece of silence?',
    goal: 'Read all input. Halt with exactly [N] on the stack, where N is the number of input bytes. Produce no output.',
    cases: ['', 'a', 'emd', '\0\n\0', 'é—', 'a'.repeat(33)].map((input, i) => ({
      name: `Test ${i + 1}`, input, output: '', stack: [new TextEncoder().encode(input).length],
    })) },
  { id: 'room-echo', title: 'Is there anybody in there?',
    goal: 'Copy every input byte to output, in order, then halt. Empty input must produce empty output.',
    cases: cases(['', 'Hello?', 'Hello?\nHello?\n', 'a\0b', 'é—\n'], s => s) },
  { id: 'room-reverse', title: 'Can you unsay something?',
    goal: 'Read all input, which is ASCII. Output its bytes in reverse order, then halt. Empty input must work too.',
    cases: cases(['', 'x', 'drawer', 'a\0b\nc', 'Never odd or even.'], s => [...s].reverse().join('')) },
  { id: 'room-caesar', title: 'What comes after the end?',
    goal: 'Input contains only uppercase A–Z, possibly empty. Replace each letter with the next one, wrapping Z to A. Output the result, then halt.',
    cases: cases(['', 'A', 'Z', 'AZBY', 'ZZZ', 'THEEND'], s => s.replace(/[A-Z]/g, c => String.fromCharCode(65 + (c.charCodeAt(0) - 64) % 26))) },
];

export function acceptsRoomEdit(type: string, text: string | null): boolean {
  if (type.startsWith('delete') || type.startsWith('history')) return true;
  if (type === 'insertLineBreak' || type === 'insertParagraph') return true;
  return type === 'insertText' && text !== null && /^[-‐‑‒–—―−\n]*$/u.test(text);
}
