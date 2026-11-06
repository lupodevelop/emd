import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import test from 'node:test';
import { checkChallenge } from '../src/lib/challenges.ts';
import { callEmd } from '../src/lib/wasm.ts';

const { instance } = await WebAssembly.instantiate(readFileSync(new URL('../public/emd.wasm', import.meta.url)));
const run = (source, input) => callEmd(instance.exports, 'emd_run', source, input);
const keys = text => [...text].map(key => '-‐‑‒–—―−'['asdfghjk'.indexOf(key)]).join('');

test('a sum must halt with exactly [3] and no output', () => {
  assert.equal(checkChallenge('three', keys('asaddagf'), run).passed, 1);
  assert.equal(checkChallenge('three', keys('asgf'), run).passed, 0);
  assert.equal(checkChallenge('three', keys('aaasaddagf'), run).passed, 0);
});

test('print A accepts the exact output and rejects a different byte', () => {
  assert.equal(checkChallenge('print-a', keys('asakddaddaakddaddahsgf'), run).passed, 1);
  assert.equal(checkChallenge('print-a', keys('ashsgf'), run).passed, 0);
});

test('echo accepts a real loop on empty, multiline, zero-byte and Unicode input', () => {
  const source = readFileSync(new URL('../../examples/cat.emd', import.meta.url), 'utf8');
  const report = checkChallenge('echo', source, run);
  assert.equal(report.passed, report.total);
  assert.ok(report.total >= 5);
});

test('hard-coding the visible echo example does not solve the challenge', () => {
  const report = checkChallenge('echo', keys('asakddaddaakddaddahsgf'), run);
  assert.equal(report.passed, 1);
  assert.ok(report.passed < report.total);
});

test('parse errors and runtime faults cannot pass', () => {
  for (const source of ['', 'x', keys('dagf')]) {
    const report = checkChallenge('three', source, run);
    assert.equal(report.passed, 0);
    assert.equal(report.results[0].ok, false);
    assert.ok(report.results[0].status);
  }
});

test('a nonterminating program fails at the VM step limit', () => {
  const report = checkChallenge('three', keys('aaafdsga'), run);
  assert.equal(report.passed, 0);
  assert.match(report.results[0].status, /step limit/);
});

test('runaway output fails without sending a huge result to the page', () => {
  const report = checkChallenge('three', keys('aaafdsashssaga'), run);
  assert.equal(report.passed, 0);
  assert.match(report.results[0].status, /output limit/);
  assert.ok(report.results[0].actual.length < 1200);
});

test('unknown challenge IDs are rejected', () => {
  assert.throws(() => checkChallenge('missing', '', run), /Unknown challenge/);
});
