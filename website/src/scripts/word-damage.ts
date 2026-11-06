// The copy stays intact: the intrusive glyphs are CSS-generated decorations.
// Clearing a gap is permanent for this visit and never captures touch scrolling.
const damageAlphabet = ['—', '–', '‐', '―', '−', '‒', '‑'];
const targets = document.querySelectorAll<HTMLElement>([
  '.hero h2', '.hero-description', '.hero-fine',
  '.layout-note', '.tools-footnote',
  '.section-heading h2', '.section-heading > p',
  '.hello-grid h2', '.hello-grid p',
  '.serious-rows h3', '.serious-rows p',
  '.paper-note p', '.install h2', '.install > p:not(.copy-feedback)',
  '.sponsors h2', '.sponsors > p', '.site-footer p',
].join(','));
let damageIndex = 0;
for (const target of targets) {
  const walker = document.createTreeWalker(target, NodeFilter.SHOW_TEXT, {
    acceptNode(node) {
      const parent = node.parentElement;
      if (!parent || parent.closest('a, button, code, pre, .word-gap, [aria-live], [role="status"]')) return NodeFilter.FILTER_REJECT;
      return /\S[ \t]+\S/.test(node.textContent ?? '') ? NodeFilter.FILTER_ACCEPT : NodeFilter.FILTER_REJECT;
    },
  });
  const nodes: Text[] = [];
  while (walker.nextNode()) nodes.push(walker.currentNode as Text);
  for (const node of nodes) {
    const fragment = document.createDocumentFragment();
    const parts = (node.textContent ?? '').split(/([ \t]+)/);
    for (let i = 0; i < parts.length; i++) {
      if (i % 2 === 1 && i > 0 && i < parts.length - 1 && parts[i - 1] && parts[i + 1]) {
        const gap = document.createElement('span');
        gap.className = 'word-gap';
        const intruder = document.createElement('span');
        intruder.className = 'word-intruder';
        intruder.setAttribute('aria-hidden', 'true');
        intruder.dataset.dash = damageAlphabet[damageIndex++ % damageAlphabet.length];
        gap.append(document.createTextNode(parts[i]));
        gap.append(intruder);
        fragment.append(gap);
      } else fragment.append(document.createTextNode(parts[i]));
    }
    node.replaceWith(fragment);
  }
}

function clearGap(target: EventTarget | null) {
  if (!(target instanceof Element)) return;
  const gap = target.closest<HTMLElement>('.word-gap');
  if (!gap || gap.classList.contains('cleared')) return;
  gap.classList.add('cleared');
}
document.addEventListener('pointerover', event => {
  if (event.pointerType === 'mouse' || event.pointerType === 'pen') clearGap(event.target);
}, { passive: true });
document.addEventListener('pointerdown', event => clearGap(event.target), { passive: true });
// Older touch browsers without Pointer Events get the same release.
if (!('PointerEvent' in window)) document.addEventListener('touchstart', event => clearGap(event.target), { passive: true });
