import { sourceLineMax, url } from '../lib/site';
import { wrapSource } from '../lib/source-layout';
import { challenges } from '../lib/challenges';
import type { ChallengeReport } from '../lib/challenges';
import { callEmd } from '../lib/wasm';
import type { EmdExports, Explanation, RunResult } from '../lib/wasm';

// Decoding and running go through emd.wasm, the real
// parser and VM. Input is restricted to the dash alphabet from the letter table,
// checked against the Rust by docs.rs; instruction validity still belongs to WASM.
const source = document.querySelector<HTMLTextAreaElement>('#kb-source')!;
const glyphByKey = new Map(
  [...document.querySelectorAll<HTMLElement>('.kb-key')].map(key => [key.querySelector('kbd')!.textContent!, key.dataset.insert!]),
);
// A newline is part of a source: it goes before decoding, wherever it falls.
const allowedGlyphs = new Set([...glyphByKey.values(), '\n']);
const allowedSource = (text: string) => [...text].every(glyph => allowedGlyphs.has(glyph));
let acceptedSource = source.value;
let acceptedStart = source.selectionStart;
let acceptedEnd = source.selectionEnd;

function rememberSource() {
  acceptedSource = source.value;
  acceptedStart = source.selectionStart;
  acceptedEnd = source.selectionEnd;
}

function inputFeedback(rejected: boolean) {
  document.querySelector('#kb-input-status')!.textContent = rejected
    ? 'Only the eight emd dashes and newlines are allowed. Spaces and other characters are rejected.'
    : '';
}

let wasm: EmdExports | undefined;
const encoder = new TextEncoder();

function refreshDecoded() {
  invalidateChallenge();
  if (allowedSource(source.value)) {
    const wrapped = wrapSource(source.value, source.selectionStart, source.selectionEnd, sourceLineMax);
    if (wrapped.value !== source.value) {
      source.value = wrapped.value;
      source.setSelectionRange(wrapped.start, wrapped.end);
    }
  }
  const text = source.value;
  if (allowedSource(text)) {
    rememberSource();
    inputFeedback(false);
  }
  const dashes = [...text.replaceAll('\n', '')].length;
  const lines = text ? text.split('\n').length : 0;
  document.querySelector('#kb-count')!.textContent = `${dashes} dashes · ${lines} line${lines === 1 ? '' : 's'}`;
  if (!wasm) return;
  const report = callEmd<Explanation>(wasm, 'emd_explain', text);
  const problems = document.querySelector('#kb-problems')!;
  problems.replaceChildren(...report.problems.map((p: string) => Object.assign(document.createElement('li'), { textContent: p })));
  const rows = report.instructions.map((i: { index: number; source: string; name: string; effect: string }) => {
    const row = document.createElement('tr');
    for (const cell of [i.index, i.source, i.name, i.effect]) row.append(Object.assign(document.createElement('td'), { textContent: String(cell) }));
    return row;
  });
  document.querySelector('#kb-decoded')!.replaceChildren(...rows);
}

// execCommand keeps the browser's undo history; setRangeText is the fallback without it.
function insertAtCursor(text: string) {
  if (!document.execCommand('insertText', false, text)) {
    source.setRangeText(text, source.selectionStart, source.selectionEnd, 'end');
    source.dispatchEvent(new Event('input'));
  }
}

// Input events wrap all valid edits, including paste, drop and middle insertions.
function insert(text: string) {
  if (!allowedSource(text)) { inputFeedback(true); return; }
  source.focus();
  insertAtCursor(text);
}

source.addEventListener('keydown', event => {
  if (event.isComposing) return;
  const glyph = glyphByKey.get(event.key);
  if (glyph && !event.ctrlKey && !event.metaKey && !event.altKey) {
    event.preventDefault();
    insert(glyph);
  }
});

source.addEventListener('beforeinput', event => {
  // Save both the content and selection before edits, including replacements.
  if (allowedSource(source.value)) rememberSource();
  if (!event.inputType.startsWith('insert')) return;
  const text = event.dataTransfer?.getData('text/plain') ?? event.data;
  // Mobile keyboards may deliver text without a useful keydown event.
  const glyph = event.inputType === 'insertText' && text !== null ? glyphByKey.get(text) : undefined;
  if (glyph && event.cancelable && !event.isComposing) {
    event.preventDefault();
    insert(glyph);
    return;
  }
  if (text !== null && !allowedSource(text)) {
    if (event.cancelable) event.preventDefault();
    inputFeedback(true);
  }
});

// Reject the entire paste/drop, rather than silently changing the program.
source.addEventListener('paste', event => {
  if (!allowedSource(event.clipboardData?.getData('text/plain') ?? '')) {
    event.preventDefault();
    inputFeedback(true);
  }
});
source.addEventListener('drop', event => {
  if (!allowedSource(event.dataTransfer?.getData('text/plain') ?? '')) {
    event.preventDefault();
    inputFeedback(true);
  }
});
source.addEventListener('input', () => {
  // Covers non-cancelable edits, IME, autofill and browser-specific input paths.
  if (!allowedSource(source.value)) {
    source.value = acceptedSource;
    source.setSelectionRange(acceptedStart, acceptedEnd);
    inputFeedback(true);
    return;
  }
  inputFeedback(false);
  refreshDecoded();
});

document.querySelectorAll<HTMLButtonElement>('[data-insert]').forEach(button => {
  button.addEventListener('click', () => insert(button.dataset.insert!));
});

const runButton = document.querySelector<HTMLButtonElement>('#kb-run')!;
runButton.addEventListener('click', () => {
  if (!wasm) return;
  if (selectedChallenge) { checkSolution(); return; }
  const input = document.querySelector<HTMLInputElement>('#kb-input')!.value;
  const result = callEmd<RunResult>(wasm, 'emd_run', source.value, input);
  document.querySelector<HTMLElement>('#kb-result')!.hidden = false;
  document.querySelector('#kb-status')!.textContent = result.status;
  document.querySelector('#kb-stack')!.textContent = JSON.stringify(result.stack);
  document.querySelector('#kb-steps')!.textContent = String(result.steps);
  document.querySelector('#kb-output')!.textContent = result.output;
});

const challengeSelect = document.querySelector<HTMLSelectElement>('#kb-challenge')!;
const challengeResult = document.querySelector<HTMLElement>('#challenge-result')!;
const challengeSummary = document.querySelector<HTMLElement>('#challenge-summary')!;
const challengeCases = document.querySelector<HTMLOListElement>('#challenge-cases')!;
const stopButton = document.querySelector<HTMLButtonElement>('#kb-stop')!;
const drafts = new Map<string, string>();
let selectedChallenge = '';
let worker: Worker | undefined;
let deadline: ReturnType<typeof setTimeout> | undefined;

function stopCheck() {
  worker?.terminate();
  worker = undefined;
  clearTimeout(deadline);
  stopButton.hidden = true;
  runButton.disabled = !wasm;
  runButton.textContent = selectedChallenge ? 'Check solution →' : 'Run the dashes →';
}

function invalidateChallenge() {
  stopCheck();
  challengeResult.hidden = true;
  challengeCases.replaceChildren();
}

function selectChallenge() {
  drafts.set(selectedChallenge, source.value);
  selectedChallenge = challengeSelect.value;
  source.value = drafts.get(selectedChallenge) ?? '';
  const challenge = challenges.find(item => item.id === selectedChallenge);
  document.querySelector<HTMLElement>('#challenge-brief')!.hidden = !challenge;
  document.querySelector('#challenge-goal')!.textContent = challenge?.goal ?? '';
  document.querySelector('#challenge-hint')!.textContent = challenge?.hint ?? '';
  document.querySelector<HTMLElement>('#kb-examples')!.hidden = !!challenge;
  document.querySelector<HTMLElement>('#kb-stdin')!.hidden = !!challenge;
  document.querySelector<HTMLElement>('#kb-result')!.hidden = true;
  const location = new URL(window.location.href);
  if (challenge) location.searchParams.set('challenge', challenge.id);
  else location.searchParams.delete('challenge');
  history.replaceState(null, '', location);
  refreshDecoded();
}

function showChallengeReport(report: ChallengeReport) {
  challengeSummary.textContent = report.passed === report.total
    ? `Solved. ${report.passed}/${report.total} tests passed.`
    : `${report.passed}/${report.total} tests passed. Keep going.`;
  challengeResult.dataset.state = report.passed === report.total ? 'passed' : 'failed';
  challengeCases.replaceChildren(...report.results.map(test => {
    const item = document.createElement('li');
    const details = document.createElement('details');
    const summary = document.createElement('summary');
    summary.textContent = `${test.ok ? '✓' : '✕'} ${test.name}`;
    const output = document.createElement('pre');
    output.textContent = `Input: ${JSON.stringify(test.input)}\nExpected: ${test.expected}\nGot: ${test.actual}\nStatus: ${test.status}`;
    details.open = !test.ok;
    details.append(summary, output);
    item.append(details);
    return item;
  }));
}

function checkSolution() {
  invalidateChallenge();
  challengeResult.hidden = false;
  challengeResult.dataset.state = 'checking';
  challengeSummary.textContent = 'Checking…';
  runButton.disabled = true;
  stopButton.hidden = false;
  try {
    const current = new Worker(new URL('./challenge-worker.ts', import.meta.url), { type: 'module' });
    worker = current;
    const fail = (message: string) => {
      if (worker !== current) return;
      stopCheck();
      challengeResult.dataset.state = 'failed';
      challengeSummary.textContent = message;
    };
    current.onmessage = ({ data }: MessageEvent<{ report?: ChallengeReport; error?: string }>) => {
      if (worker !== current) return;
      if (data.report) { stopCheck(); showChallengeReport(data.report); }
      else fail(data.error ?? 'Could not check the solution. Try again.');
    };
    current.onerror = () => fail('Could not check the solution. Try again.');
    deadline = setTimeout(() => fail('Time limit reached. Check for a loop that never ends.'), 10_000);
    current.postMessage({ id: selectedChallenge, source: source.value, wasmUrl: url('emd.wasm') });
  } catch {
    stopCheck();
    challengeResult.dataset.state = 'failed';
    challengeSummary.textContent = 'Could not start the runner. Reload to try again.';
  }
}

stopButton.addEventListener('click', () => {
  stopCheck();
  challengeSummary.textContent = 'Stopped.';
});
challengeSelect.addEventListener('change', selectChallenge);
const requested = new URL(window.location.href).searchParams.get('challenge');
if (challenges.some(item => item.id === requested)) challengeSelect.value = requested!;
else if (window.location.hash === '#challenges') challengeSelect.value = challenges[0].id;
selectChallenge();

document.querySelector('#kb-copy')!.addEventListener('click', () => navigator.clipboard?.writeText(source.value));
document.querySelector('#kb-download')!.addEventListener('click', () => {
  const link = document.createElement('a');
  link.href = URL.createObjectURL(new Blob([encoder.encode(source.value)], { type: 'application/octet-stream' }));
  link.download = 'program.emd';
  link.click();
  URL.revokeObjectURL(link.href);
});
const exampleSelect = document.querySelector<HTMLSelectElement>('#kb-example')!;
exampleSelect.addEventListener('change', () => {
  document.querySelector<HTMLAnchorElement>('#kb-example-assembly')!.href = url(`examples/${encodeURIComponent(exampleSelect.value)}.asm`);
});
const loadExample = document.querySelector<HTMLButtonElement>('#kb-load-example')!;
loadExample.addEventListener('click', async () => {
  const selected = exampleSelect.selectedOptions[0];
  loadExample.disabled = true;
  exampleSelect.disabled = true;
  try {
    const response = await fetch(url(`examples/${encodeURIComponent(selected.value)}.emd`));
    if (!response.ok) throw new Error('Example unavailable');
    source.value = await response.text();
    document.querySelector<HTMLInputElement>('#kb-input')!.value = selected.dataset.input ?? '';
    document.querySelector<HTMLElement>('#kb-result')!.hidden = true;
    refreshDecoded();
  } catch {
    document.querySelector('#kb-input-status')!.textContent = 'Could not load this example. Try again.';
  } finally {
    loadExample.disabled = false;
    exampleSelect.disabled = false;
  }
});
document.querySelector('#kb-clear')!.addEventListener('click', () => {
  source.value = '';
  document.querySelector<HTMLElement>('#kb-result')!.hidden = true;
  refreshDecoded();
});

WebAssembly.instantiateStreaming(fetch(url('emd.wasm'))).then(({ instance }) => {
  wasm = instance.exports as unknown as EmdExports;
  document.querySelector('#kb-runtime-status')!.textContent = '';
  refreshDecoded();
}).catch(() => {
  document.querySelector('#kb-runtime-status')!.textContent = 'Could not load the runner. Reload to try again.';
});
