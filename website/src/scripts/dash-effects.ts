// A shared, bounded animation loop: every particle is a horizontal dash.
const field = document.querySelector<HTMLCanvasElement>('#dash-field');
const logo = document.querySelector<HTMLCanvasElement>('#dash-logo');
const control = document.querySelector<HTMLButtonElement>('.logo-control');
const fieldContext = field?.getContext('2d', { alpha: true });
const logoContext = logo?.getContext('2d', { alpha: true });
const motion = matchMedia('(prefers-reduced-motion: reduce)');

if (field && fieldContext) {
  const canvas = field;
  const ctx = fieldContext;
  type Dash = { x: number; y: number; z: number; length: number; speed: number; phase: number };
  type LogoDash = { x: number; y: number; homeX: number; homeY: number; vx: number; vy: number; length: number; row: number; seed: number };
  type Ripple = { x: number; y: number; start: number };
  let width = 0, height = 0, logoWidth = 0, logoHeight = 0, dpr = 1;
  let particles: Dash[] = [], logoParticles: LogoDash[] = [], ripples: Ripple[] = [];
  let accent = '#bcace8', ink = '#f0e9e0', dim = '#6d617e';
  let pointer = { x: -10000, y: -10000 };
  let frame = 0, lastTime = 0, lastPaint = 0, clock = 0, logoVisible = true;
  let resizeFrame = 0;

  function colors() {
    const style = getComputedStyle(document.documentElement);
    accent = style.getPropertyValue('--accent').trim();
    ink = style.getPropertyValue('--ink').trim();
    dim = style.getPropertyValue('--dim').trim();
  }

  function resize() {
    dpr = Math.min(devicePixelRatio || 1, 1.5);
    width = innerWidth;
    height = innerHeight;
    canvas.width = Math.round(width * dpr);
    canvas.height = Math.round(height * dpr);
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    const count = Math.min(1000, Math.round(width * height / 1500));
    particles = Array.from({ length: count }, () => ({ x: Math.random() * width, y: Math.random() * height, z: .2 + Math.random() * .8, length: 3 + Math.random() * 16, speed: 4 + Math.random() * 13, phase: Math.random() * Math.PI * 2 }));
    if (logo && logoContext && control) {
      const bounds = logo.getBoundingClientRect();
      const svg = control.querySelector('svg')!;
      const matrix = svg.getScreenCTM();
      if (!matrix || !bounds.width || !bounds.height) return;
      const scale = Math.hypot(matrix.a, matrix.b);
      logoWidth = bounds.width;
      logoHeight = bounds.height;
      logo.width = Math.round(logoWidth * dpr);
      logo.height = Math.round(logoHeight * dpr);
      logoContext.setTransform(dpr, 0, 0, dpr, 0, 0);
      logoParticles = [];
      const path = control.querySelector<SVGPathElement>('[data-logo-path]')!;
      const mask = document.createElement('canvas');
      const box = svg.viewBox.baseVal;
      mask.width = Math.ceil(box.width * 2);
      mask.height = Math.ceil(box.height * 2);
      const maskContext = mask.getContext('2d', { willReadFrequently: true })!;
      maskContext.scale(2, 2);
      maskContext.translate(-box.x, -box.y);
      maskContext.lineWidth = Number(svg.getAttribute('stroke-width'));
      maskContext.stroke(new Path2D(path.getAttribute('d')!));
      const pixels = maskContext.getImageData(0, 0, mask.width, mask.height).data;
      // Sample the original SVG stroke into horizontal dashes.
      for (let y = 1; y < box.height; y += 2.2) {
        for (let x = 0; x < box.width - 1; x += 2.4) {
          const pixel = (Math.floor(y * 2) * mask.width + Math.floor((x + 1) * 2)) * 4;
          if (pixels[pixel + 3] < 128) continue;
          const home = new DOMPoint(box.x + x, box.y + y).matrixTransform(matrix);
          const homeX = home.x - bounds.left;
          const homeY = home.y - bounds.top;
          logoParticles.push({ homeX, homeY, x: homeX, y: homeY, vx: 0, vy: 0, length: 1.9 * scale, row: Math.floor(y / box.height * 9), seed: Math.random() });
        }
      }
      if (!motion.matches) control.classList.add('particles-ready');
      else control.classList.remove('particles-ready');
    }
    colors();
    if (motion.matches) draw(performance.now(), 0);
  }

  function draw(now: number, dt: number) {
    ctx.clearRect(0, 0, width, height);
    const scroll = window.scrollY;
    // Higher density in the hero and at the edges; keep reading columns quiet.
    const hero = Math.max(0, 1 - scroll / 850);
    ripples = ripples.filter(ripple => now - ripple.start < 1800);
    for (const p of particles) {
      if (!motion.matches) {
        p.x += p.speed * p.z * dt;
        p.y += Math.sin(clock * .3 + p.phase) * dt * 3;
        if (p.x > width + 30) p.x = -30;
        if (p.y < -20) p.y = height + 10;
        if (p.y > height + 20) p.y = -10;
      }
      const depth = p.z;
      const flow = motion.matches ? 0 : Math.sin(p.x * .004 + clock * .26 + depth * 3) * 27 * depth;
      const parallax = pointer.x < 0 ? 0 : (pointer.x / Math.max(width, 1) - .5) * depth * 9;
      let x = p.x + parallax;
      let y = p.y + flow - (scroll * depth * .07) % height;
      if (y < 0) y += height;
      const distance = Math.hypot(x - pointer.x, y - pointer.y);
      const proximity = motion.matches ? 0 : Math.max(0, 1 - distance / 180);
      if (proximity) { x += (x - pointer.x) * proximity * .28; y += (y - pointer.y) * proximity * .28; }
      let rippleLight = 0;
      for (const ripple of ripples) {
        const radius = (now - ripple.start) * .45;
        const distanceToWave = Math.abs(Math.hypot(x - ripple.x, y - ripple.y) - radius);
        if (distanceToWave < 60) {
          const strength = (1 - distanceToWave / 60) * (1 - (now - ripple.start) / 1800);
          rippleLight += strength;
          x += strength * 20;
        }
      }
      const edge = Math.min(1, Math.abs(x / width - .5) * 2.2);
      const readingMask = .14 + edge * .6 + hero * .35;
      ctx.globalAlpha = Math.min(.75, (.12 + depth * .28 + proximity * .5 + rippleLight * .8) * readingMask);
      ctx.fillStyle = proximity > .25 || rippleLight > .2 ? ink : p.z > .65 ? accent : dim;
      ctx.fillRect(x, y, p.length * depth + proximity * 13 + rippleLight * 25, depth > .7 ? 1.4 : .8);
    }
    ctx.globalAlpha = 1;

    if (!logo || !logoContext || !control || !logoVisible) return;
    const lc = logoContext;
    lc.clearRect(0, 0, logoWidth, logoHeight);
    if (motion.matches) return;
    const bounds = logo.getBoundingClientRect();
    const mx = pointer.x - bounds.left, my = pointer.y - bounds.top;
    const hovering = mx > 0 && mx < logoWidth && my > 0 && my < logoHeight;
    const cycle = clock % 6.7;
    const tearing = cycle > 5.95 && cycle < 6.25;
    const tearRow = Math.floor(clock * 18) % 9;
    const step = Math.min(dt * 60, 2);
    for (const p of logoParticles) {
      const dx = p.x - mx, dy = p.y - my;
      const distance = Math.hypot(dx, dy);
      if (hovering && distance < 85 && distance > .1) {
        const force = (1 - distance / 85) * 1.6;
        p.vx += dx / distance * force * step;
        p.vy += dy / distance * force * step;
      }
      p.vx += (p.homeX - p.x) * .035 * step;
      p.vy += (p.homeY - p.y) * .035 * step;
      p.vx *= Math.pow(.82, step);
      p.vy *= Math.pow(.82, step);
      p.x += p.vx * step;
      p.y += p.vy * step;
      const torn = tearing && (p.row === tearRow || p.row === (tearRow + 3) % 9);
      const offset = torn ? Math.sin(clock * 70 + p.row) * 22 : 0;
      const shimmer = .75 + Math.sin(clock * 1.5 + p.seed * 25) * .2;
      lc.globalAlpha = shimmer;
      lc.fillStyle = torn || (hovering && distance < 100) ? ink : accent;
      lc.fillRect(p.x + offset, p.y, p.length + (torn ? 7 : 0), Math.max(1.2, logoWidth / 600));
      if (torn) {
        lc.globalAlpha = .25;
        lc.fillStyle = accent;
        lc.fillRect(p.x - offset * 2, p.y + 3, p.length * 2, 1);
      }
    }
    lc.globalAlpha = 1;
  }

  function animate(now: number) {
    frame = requestAnimationFrame(animate);
    if (now - lastPaint < 1000 / 30) return;
    const dt = lastTime ? Math.min((now - lastTime) / 1000, .05) : .016;
    lastTime = now;
    lastPaint = now;
    clock += dt;
    draw(now, dt);
  }

  function restart() {
    cancelAnimationFrame(frame);
    lastTime = 0;
    if (document.hidden || motion.matches) { draw(performance.now(), 0); return; }
    frame = requestAnimationFrame(animate);
  }

  window.addEventListener('pointermove', event => { pointer.x = event.clientX; pointer.y = event.clientY; }, { passive: true });
  document.addEventListener('pointerleave', () => { pointer.x = pointer.y = -10000; });
  window.addEventListener('pointerdown', event => {
    if (!motion.matches) ripples.push({ x: event.clientX, y: event.clientY, start: performance.now() });
    if (ripples.length > 5) ripples.shift();
  }, { passive: true });
  control?.addEventListener('click', () => {
    if (motion.matches) return;
    for (const p of logoParticles) { p.vx += (Math.random() - .5) * 24; p.vy += (Math.random() - .5) * 14; }
  });
  const scheduleResize = () => { cancelAnimationFrame(resizeFrame); resizeFrame = requestAnimationFrame(resize); };
  window.addEventListener('resize', scheduleResize, { passive: true });
  if (control) new ResizeObserver(scheduleResize).observe(control);
  document.addEventListener('visibilitychange', restart);
  motion.addEventListener('change', () => { resize(); restart(); });
  new MutationObserver(() => { colors(); if (motion.matches) draw(performance.now(), 0); }).observe(document.documentElement, { attributes: true, attributeFilter: ['data-theme'] });
  if (control) new IntersectionObserver(entries => { logoVisible = entries[0].isIntersecting; }).observe(control);
  resize();
  restart();
}
