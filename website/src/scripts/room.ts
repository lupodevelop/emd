import { roomChallenges, acceptsRoomEdit } from '../lib/room';
import { sourceLineMax, url } from '../lib/site';
import { wrapSource } from '../lib/source-layout';
import type { ChallengeReport } from '../lib/challenges';

const source = document.querySelector<HTMLTextAreaElement>('#room-source')!;
const check = document.querySelector<HTMLButtonElement>('#room-check')!;
const stop = document.querySelector<HTMLButtonElement>('#room-stop')!;
const next = document.querySelector<HTMLButtonElement>('#room-next')!;
const feedback = document.querySelector<HTMLElement>('#room-feedback')!;
const tests = document.querySelector<HTMLOListElement>('#room-tests')!;
const doors = [...document.querySelectorAll<HTMLButtonElement>('[data-door]')];
const storageKey = 'emd-dash-room-v1';
const drafts = roomChallenges.map(() => '');
const solved = roomChallenges.map(() => false);
let index = 0;
let accepted = '';
let worker: Worker | undefined;
let timer: ReturnType<typeof setTimeout> | undefined;

try {
  const saved = JSON.parse(localStorage.getItem(storageKey) ?? 'null');
  if (saved && Array.isArray(saved.drafts) && Array.isArray(saved.solved)) {
    drafts.forEach((_, i) => {
      if (typeof saved.drafts[i] === 'string' && /^[-‐‑‒–—―−\n]*$/u.test(saved.drafts[i])) drafts[i] = saved.drafts[i];
      solved[i] = saved.solved[i] === true && (i === 0 || solved[i - 1]);
    });
    if (Number.isInteger(saved.index)) index = Math.max(0, Math.min(saved.index, unlocked()));
  }
} catch {}

function unlocked() {
  const first = solved.indexOf(false);
  return first < 0 ? solved.length - 1 : first;
}
function save() {
  try { localStorage.setItem(storageKey, JSON.stringify({ drafts, solved, index })); } catch {}
}
function stopRun() {
  worker?.terminate();
  worker = undefined;
  clearTimeout(timer);
  check.disabled = false;
  stop.hidden = true;
}
function resetResult() {
  stopRun();
  tests.replaceChildren();
  feedback.textContent = '';
  next.hidden = true;
}
function updateDoors() {
  doors.forEach((door, i) => {
    door.disabled = i > unlocked();
    if (i === index) door.setAttribute('aria-current', 'step');
    else door.removeAttribute('aria-current');
    door.toggleAttribute('data-solved', solved[i]);
    door.setAttribute('aria-label', `Door ${i + 1}${solved[i] ? ', solved' : i > unlocked() ? ', locked' : ''}`);
  });
}
function updateCount() {
  const count = [...source.value.replaceAll('\n', '')].length;
  document.querySelector('#room-size')!.textContent = `${count} dash${count === 1 ? '' : 'es'}`;
}
function showDoor(i: number, focus = true) {
  if (i > unlocked()) return;
  resetResult();
  index = i;
  source.value = drafts[index];
  accepted = source.value;
  const challenge = roomChallenges[index];
  document.querySelector('#room-number')!.textContent = `DOOR ${String(index + 1).padStart(2, '0')} / 10`;
  document.querySelector('#room-question')!.textContent = challenge.title;
  document.querySelector('#room-spec')!.textContent = challenge.goal;
  next.hidden = !solved[index] || index === 9;
  document.querySelector<HTMLElement>('#room-finished')!.hidden = !solved.every(Boolean);
  updateDoors();
  updateCount();
  save();
  if (focus) document.querySelector<HTMLElement>('#room-question')!.focus();
}
function rejectEdit() {
  feedback.textContent = 'Only dashes, entered by hand.';
}
source.addEventListener('paste', event => { event.preventDefault(); rejectEdit(); });
source.addEventListener('drop', event => { event.preventDefault(); rejectEdit(); });
source.addEventListener('beforeinput', event => {
  if (!acceptsRoomEdit(event.inputType, event.data)) {
    if (event.cancelable) event.preventDefault();
    rejectEdit();
  }
});
source.addEventListener('input', event => {
  const edit = event as InputEvent;
  if ((edit.inputType && !acceptsRoomEdit(edit.inputType, edit.data)) || !/^[-‐‑‒–—―−\n]*$/u.test(source.value)) {
    source.value = accepted;
    rejectEdit();
    return;
  }
  const wrapped = wrapSource(source.value, source.selectionStart, source.selectionEnd, sourceLineMax);
  source.value = wrapped.value;
  source.setSelectionRange(wrapped.start, wrapped.end);
  accepted = source.value;
  drafts[index] = source.value;
  resetResult();
  updateCount();
  save();
});
for (const button of document.querySelectorAll<HTMLButtonElement>('[data-dash]')) {
  button.addEventListener('click', () => {
    source.focus();
    if (!document.execCommand('insertText', false, button.dataset.dash!)) {
      source.setRangeText(button.dataset.dash!, source.selectionStart, source.selectionEnd, 'end');
      source.dispatchEvent(new Event('input'));
    }
  });
}
document.querySelector('#room-clear')!.addEventListener('click', () => {
  source.value = '';
  source.dispatchEvent(new Event('input'));
  source.focus();
});
for (const door of doors) door.addEventListener('click', () => showDoor(Number(door.dataset.door)));
next.addEventListener('click', () => showDoor(index + 1));
stop.addEventListener('click', () => { stopRun(); feedback.textContent = 'Stopped.'; });

check.addEventListener('click', () => {
  resetResult();
  feedback.textContent = 'Trying the lock…';
  check.disabled = true;
  stop.hidden = false;
  try {
    const current = new Worker(new URL('./challenge-worker.ts', import.meta.url), { type: 'module' });
    worker = current;
    const fail = (message: string) => {
      if (worker !== current) return;
      stopRun();
      feedback.textContent = message;
    };
    current.onmessage = ({ data }: MessageEvent<{ report?: ChallengeReport; error?: string }>) => {
      if (worker !== current) return;
      if (!data.report) { fail('The runner could not start. Try again.'); return; }
      stopRun();
      const report = data.report;
      const passed = report.passed === report.total;
      feedback.textContent = passed ? 'The lock gives way.' : `${report.passed} / ${report.total} tests passed. The door stays shut.`;
      tests.replaceChildren(...report.results.map((result, i) => {
        const item = document.createElement('li');
        item.textContent = `${result.ok ? '✓' : '✕'} Test ${i + 1}`;
        item.setAttribute('aria-label', `Test ${i + 1}: ${result.ok ? 'passed' : 'failed'}`);
        return item;
      }));
      if (passed) {
        solved[index] = true;
        updateDoors();
        next.hidden = index === roomChallenges.length - 1;
        save();
        if (solved.every(Boolean)) {
          document.querySelector<HTMLElement>('#room-finished')!.hidden = false;
          document.querySelector<HTMLElement>('#room-finished-title')!.focus();
        }
      }
    };
    current.onerror = () => fail('The runner could not start. Reload and try again.');
    timer = setTimeout(() => fail('The lock timed out. Your program must finish.'), 10_000);
    current.postMessage({ id: roomChallenges[index].id, source: source.value, wasmUrl: url('emd.wasm'), room: true });
  } catch {
    stopRun();
    feedback.textContent = 'The runner could not start. Reload and try again.';
  }
});
showDoor(index, false);
