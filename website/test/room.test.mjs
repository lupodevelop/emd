import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import test from 'node:test';
import { roomChallenges, acceptsRoomEdit } from '../src/lib/room.ts';
import { checkChallenge } from '../src/lib/challenges.ts';
import { callEmd } from '../src/lib/wasm.ts';

const { instance } = await WebAssembly.instantiate(readFileSync(new URL('../public/emd.wasm', import.meta.url)));
const run = (source, input) => callEmd(instance.exports, 'emd_run', source, input);
const glyphs = '-‐‑‒–—―−';
const keys = text => [...text].map(key => glyphs['asdfghjk'.indexOf(key)]).join('');

test('the room has ten distinct doors and no hints', () => {
  assert.equal(roomChallenges.length, 10);
  assert.equal(new Set(roomChallenges.map(c => c.id)).size, 10);
  for (const challenge of roomChallenges) {
    assert.ok(challenge.goal && challenge.title && challenge.cases.length);
    assert.equal('hint' in challenge, false);
  }
});

test('the room accepts only dashes, rejects paste, drop and letter shortcuts', () => {
  assert.equal(acceptsRoomEdit('insertText', glyphs), true);
  assert.equal(acceptsRoomEdit('insertText', 'a'), false);
  assert.equal(acceptsRoomEdit('insertText', ' '), false);
  assert.equal(acceptsRoomEdit('insertFromPaste', glyphs), false);
  assert.equal(acceptsRoomEdit('insertFromDrop', glyphs), false);
  assert.equal(acceptsRoomEdit('insertReplacementText', glyphs), false);
  assert.equal(acceptsRoomEdit('deleteContentBackward', null), true);
});

test('the first door requires a clean halt; malformed and faulting programs fail', () => {
  assert.equal(checkChallenge('room-silence', keys('gf'), run, roomChallenges).passed, 1);
  for (const source of ['', 'x', keys('aagf'), keys('ssgf')]) {
    assert.equal(checkChallenge('room-silence', source, run, roomChallenges).passed, 0);
  }
});

test('a canned answer cannot pass the echo door', () => {
  const source = readFileSync(new URL('../../examples/cat.emd', import.meta.url), 'utf8');
  const report = checkChallenge('room-echo', source, run, roomChallenges);
  assert.equal(report.passed, report.total);
  assert.equal(checkChallenge('room-echo', keys('gf'), run, roomChallenges).passed, 1);
});

// Fixed-width constants make branch offsets independent of their values.
const instructionKeys = new Map(JSON.parse(readFileSync(new URL('../src/lib/instructions.json', import.meta.url))).map(i => [i.name, i.keys]));
function assemble(tokens) {
  const labels = new Map();
  let pc = 0;
  for (const token of tokens) {
    if (typeof token === 'string' && token.endsWith(':')) labels.set(token.slice(0, -1), pc);
    else pc += typeof token === 'number' ? 27 : Array.isArray(token) ? 28 : 1;
  }
  const constant = n => ['PUSH 0', 'PUSH 0', ...Math.abs(n).toString(8).padStart(4, '0').split('').flatMap(d =>
    ['PUSH 7', 'PUSH 1', 'ADD', 'MUL', `PUSH ${d}`, 'ADD']), n < 0 ? 'SUB' : 'ADD'];
  pc = 0;
  const code = [];
  for (const token of tokens) {
    if (typeof token === 'string' && token.endsWith(':')) continue;
    const chunk = typeof token === 'number' ? constant(token)
      : Array.isArray(token) ? [...constant(labels.get(token[1]) - (pc + 27)), token[0]] : [token];
    code.push(...chunk);
    pc += chunk.length;
  }
  return keys(code.map(op => { assert.ok(instructionKeys.has(op), op); return instructionKeys.get(op); }).join('')).match(/.{1,32}/gu).join('\n');
}
const solutions = [
  ['HALT'],
  [42, 'HALT'],
  [65, 'WRITE', 'HALT'],
  [83, 'WRITE', 79, 'WRITE', 83, 'WRITE', 'HALT'],
  ['READ', 'WRITE', 'HALT'],
  ['READ', 'READ', 'WRITE', 'WRITE', 'HALT'],
  [0, 'loop:', 'READ', 0, 'LT', ['JNZ', 'end'], 1, 'ADD', ['JMP', 'loop'], 'end:', 'HALT'],
  ['loop:', 'READ', 'DUP', 0, 'LT', ['JNZ', 'end'], 'WRITE', ['JMP', 'loop'], 'end:', 'DROP', 'HALT'],
  [-1, 'loop:', 'READ', 'DUP', 0, 'LT', ['JNZ', 'flush'], ['JMP', 'loop'], 'flush:', 'DROP',
    'out:', 'DUP', 0, 'LT', ['JNZ', 'end'], 'WRITE', ['JMP', 'out'], 'end:', 'DROP', 'HALT'],
  ['loop:', 'READ', 'DUP', 0, 'LT', ['JNZ', 'end'], 65, 'SUB', 1, 'ADD', 26, 'MOD', 65, 'ADD', 'WRITE', ['JMP', 'loop'], 'end:', 'DROP', 'HALT'],
];
for (const [index, challenge] of roomChallenges.entries()) {
  test(`real WASM validates every case for door ${index + 1}: ${challenge.title}`, () => {
    const report = checkChallenge(challenge.id, assemble(solutions[index]), run, roomChallenges);
    assert.equal(report.passed, report.total, JSON.stringify(report.results.filter(r => !r.ok)));
    if (index > 0) assert.ok(checkChallenge(challenge.id, keys('gf'), run, roomChallenges).passed < report.total);
  });
}
