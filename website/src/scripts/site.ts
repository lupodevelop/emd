import { alphabet, themes } from '../lib/site';

const root = document.documentElement;
const reducedMotion = window.matchMedia('(prefers-reduced-motion: reduce)');

function syncTheme() {
  const selected = themes.find(theme => theme.id === root.dataset.theme) ?? themes[0];
  document.querySelectorAll<HTMLButtonElement>('[data-set-theme]').forEach(button => button.setAttribute('aria-pressed', String(button.dataset.setTheme === selected.id)));
  const label = document.querySelector('.theme-name');
  if (label) label.textContent = selected.name;
  document.querySelector('meta[name="theme-color"]')?.setAttribute('content', getComputedStyle(root).getPropertyValue('--bg').trim());
}

document.querySelectorAll<HTMLButtonElement>('[data-set-theme]').forEach(button => {
  button.addEventListener('click', () => {
    if (button.dataset.setTheme === root.dataset.theme) return;
    const update = () => {
      root.dataset.theme = button.dataset.setTheme;
      try { localStorage.setItem('emd-theme', root.dataset.theme ?? 'ash'); } catch {}
      syncTheme();
    };
    if (document.startViewTransition && !reducedMotion.matches) document.startViewTransition(update);
    else update();
  });
});
syncTheme();

document.querySelectorAll<HTMLButtonElement>('[data-glyph]').forEach(button => {
  button.addEventListener('click', () => {
    const glyph = alphabet[Number(button.dataset.glyph)];
    document.querySelectorAll('[data-glyph]').forEach(item => item.setAttribute('aria-pressed', String(item === button)));
    document.querySelector('#glyph-name')!.textContent = glyph.name;
    document.querySelector('#glyph-unicode')!.textContent = ` / U+${glyph.code}`;
    document.querySelector('#glyph-verdict')!.textContent = glyph.verdict;
  });
});

// A fixed trace of the real four-instruction example, not a second VM implementation.
const demoTerminal = document.querySelector<HTMLElement>('#demo-terminal');
document.querySelectorAll<HTMLButtonElement>('[data-code-view-button]').forEach(button => {
  button.addEventListener('click', () => {
    const view = button.dataset.codeViewButton;
    if (!demoTerminal || (view !== 'expanded' && view !== 'compact')) return;
    demoTerminal.dataset.codeView = view;
    document.querySelectorAll<HTMLButtonElement>('[data-code-view-button]').forEach(item => item.setAttribute('aria-pressed', String(item === button)));
    const note = document.querySelector('#code-view-note');
    if (note) note.textContent = view === 'compact' ? 'The actual source. No spaces. No mercy.' : 'One instruction per pair. Room to think.';
  });
});

const trace = [
  { stack: '[ ]', status: 'Ready to make a point.' },
  { stack: '[ 1 ]', status: 'PUSH 1 / a modest beginning.' },
  { stack: '[ 1, 2 ]', status: 'PUSH 2 / the plot thickens.' },
  { stack: '[ 3 ]', status: 'ADD / arithmetic has occurred.' },
  { stack: '[ 3 ]', status: 'HALT / all that for three.' },
];
let step = 0;
let timer: ReturnType<typeof setInterval> | undefined;
const run = document.querySelector<HTMLButtonElement>('#run-demo');
const stepButton = document.querySelector<HTMLButtonElement>('#step-demo');
function paintTrace() {
  document.querySelector('#stack')!.textContent = trace[step].stack;
  document.querySelector('#execution-status')!.textContent = trace[step].status;
  document.querySelectorAll<HTMLElement>('[data-instruction]').forEach((item, i) => {
    item.classList.toggle('executed', i < step);
    item.classList.toggle('current', i === step - 1);
  });
  if (run) run.textContent = step === 4 ? 'Run it again ↺' : 'Run the dashes →';
  if (stepButton) stepButton.disabled = step === 4;
}
function stopTrace() { clearInterval(timer); timer = undefined; if (run) run.disabled = false; }
run?.addEventListener('click', () => {
  stopTrace();
  if (step === 4) step = 0;
  if (reducedMotion.matches) { step = 4; paintTrace(); return; }
  run.disabled = true;
  timer = setInterval(() => {
    step = Math.min(step + 1, 4);
    paintTrace();
    if (step === 4) stopTrace();
  }, 650);
});
stepButton?.addEventListener('click', () => { stopTrace(); step = Math.min(step + 1, 4); paintTrace(); });
document.querySelector('#reset-demo')?.addEventListener('click', () => { stopTrace(); step = 0; paintTrace(); });

document.querySelectorAll<HTMLButtonElement>('[data-copy]').forEach(button => {
  button.addEventListener('click', async () => {
    const text = document.getElementById(button.dataset.copy!)?.textContent;
    if (!text) return;
    const feedback = document.querySelector('#copy-feedback');
    try {
      await navigator.clipboard.writeText(text);
      if (feedback) feedback.textContent = 'Copied. A questionable decision, efficiently made.';
    } catch {
      if (feedback) feedback.textContent = 'Copy unavailable. Select the command and copy it manually.';
    }
  });
});
