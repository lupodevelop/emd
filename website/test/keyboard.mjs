#!/usr/bin/env node
// The keyboard page in headless Chrome, with real key, mouse and clipboard events over DevTools.
// Needs a built site (cd website && npm run build), Chrome and Node 22 or later.
// EMD_BIN names the CLI to compare with, CHROME the browser.
import { spawn, spawnSync } from 'node:child_process';
import { existsSync, mkdirSync, mkdtempSync, readFileSync, readdirSync, rmSync, statSync } from 'node:fs';
import { createServer } from 'node:http';
import { tmpdir } from 'node:os';
import { extname, join, normalize } from 'node:path';

const DIST = new URL('../dist', import.meta.url).pathname;
const EMD = process.env.EMD_BIN ?? 'emd';
const CHROME = process.env.CHROME ?? '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
if (!existsSync(`${DIST}/keyboard/index.html`)) { console.error('no built site: cd website && npm run build'); process.exit(2); }

const TYPES = { '.html': 'text/html', '.js': 'text/javascript', '.css': 'text/css', '.wasm': 'application/wasm', '.svg': 'image/svg+xml' };
const BASE = '/emd/';
const server = createServer((request, response) => {
  const path = normalize(decodeURIComponent(new URL(request.url, 'http://x').pathname));
  const file = join(DIST, (path.endsWith('/') ? `${path}index.html` : path).slice(BASE.length));
  if (!path.startsWith(BASE) || !file.startsWith(DIST) || !existsSync(file) || statSync(file).isDirectory()) { response.writeHead(404).end(); return; }
  response.writeHead(200, { 'content-type': TYPES[extname(file)] ?? 'application/octet-stream' }).end(readFileSync(file));
});
await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
const ORIGIN = `http://127.0.0.1:${server.address().port}`;

const work = mkdtempSync(join(tmpdir(), 'emd-keyboard-'));
const profile = `${work}/profile`, downloads = `${work}/downloads`;
mkdirSync(downloads);
const chrome = spawn(CHROME,
  ['--headless=new', '--remote-debugging-port=0', `--user-data-dir=${profile}`, '--no-first-run', '--no-default-browser-check', 'about:blank'],
  { stdio: 'ignore' });
const sleep = ms => new Promise(r => setTimeout(r, ms));
let port; for (let i = 0; i < 200 && !port; i++) { await sleep(100); const f = `${profile}/DevToolsActivePort`; if (existsSync(f)) port = readFileSync(f, 'utf8').split('\n')[0]; }
const targets = await (await fetch(`http://127.0.0.1:${port}/json`)).json();
const page = targets.find(t => t.type === 'page');
const ws = new WebSocket(page.webSocketDebuggerUrl);
await new Promise(r => ws.addEventListener('open', r));
let id = 0; const waiting = new Map(), problems = [];
ws.addEventListener('message', m => {
  const d = JSON.parse(m.data);
  if (d.id && waiting.has(d.id)) { const { ok, no } = waiting.get(d.id); waiting.delete(d.id); d.error ? no(new Error(JSON.stringify(d.error))) : ok(d.result); return; }
  if (d.method === 'Runtime.exceptionThrown') problems.push(`exception: ${d.params.exceptionDetails.exception?.description ?? d.params.exceptionDetails.text}`);
  if (d.method === 'Runtime.consoleAPICalled' && d.params.type === 'error') problems.push(`console.error: ${JSON.stringify(d.params.args.map(a => a.value))}`);
  if (d.method === 'Log.entryAdded' && d.params.entry.level === 'error') problems.push(`log: ${d.params.entry.text} ${d.params.entry.url ?? ''}`);
  if (d.method === 'Network.responseReceived' && d.params.response.status >= 400) problems.push(`http ${d.params.response.status}: ${d.params.response.url}`);
});
const cdp = (method, params = {}) => new Promise((ok, no) => { const n = ++id; waiting.set(n, { ok, no }); ws.send(JSON.stringify({ id: n, method, params })); });
const js = async expr => { const r = await cdp('Runtime.evaluate', { expression: expr, awaitPromise: true, returnByValue: true, userGesture: true }); if (r.exceptionDetails) throw new Error(r.exceptionDetails.exception?.description ?? r.exceptionDetails.text); return r.result.value; };

let passed = 0, failed = 0;
const check = (name, good, detail = '') => { good ? passed++ : failed++; console.log(`${good ? 'ok  ' : 'FAIL'} ${name}${good ? '' : ` :: ${detail}`}`); };
const eq = (name, got, want) => check(name, JSON.stringify(got) === JSON.stringify(want), `got ${JSON.stringify(got)} want ${JSON.stringify(want)}`);

const value = () => js(`document.querySelector('#kb-source').value`);
const caret = () => js(`document.querySelector('#kb-source').selectionStart`);
const status = () => js(`document.querySelector('#kb-input-status').textContent`);
const count = () => js(`document.querySelector('#kb-count').textContent`);
const rows = () => js(`document.querySelectorAll('#kb-decoded tr').length`);
const issues = () => js(`[...document.querySelectorAll('#kb-problems li')].map(l => l.textContent)`);

const CODES = { ' ': 'Space' };
async function key(k, { modifiers = 0, commands, text } = {}) {
  const code = CODES[k] ?? (k.length === 1 ? `Key${k.toUpperCase()}` : k);
  const vk = k === 'Enter' ? 13 : k === 'Backspace' ? 8 : k.toUpperCase().charCodeAt(0);
  const t = text ?? (modifiers ? undefined : k === 'Enter' ? '\r' : k.length === 1 ? k : undefined);
  await cdp('Input.dispatchKeyEvent', { type: t ? 'keyDown' : 'rawKeyDown', key: k, code, windowsVirtualKeyCode: vk, nativeVirtualKeyCode: vk, modifiers, text: t, unmodifiedText: t, commands });
  await cdp('Input.dispatchKeyEvent', { type: 'keyUp', key: k, code, windowsVirtualKeyCode: vk, nativeVirtualKeyCode: vk, modifiers });
}
async function click(selector) {
  const sel = JSON.stringify(selector);
  await js(`document.querySelector(${sel}).scrollIntoView({block:'center'})`);
  // The page scrolls smoothly: wait until the target stops moving, then check it is what the point hits.
  let r, last = '';
  for (let i = 0; i < 100; i++) {
    r = await js(`(()=>{const e=document.querySelector(${sel}),r=e.getBoundingClientRect(),x=r.x+r.width/2,y=r.y+r.height/2,h=document.elementFromPoint(x,y);return {x,y,hit:!!h&&(h===e||e.contains(h))}})()`);
    const now = `${r.x},${r.y}`;
    if (now === last && r.hit) break;
    last = now; await sleep(40);
  }
  if (!r.hit) throw new Error(`nothing clickable at ${selector}`);
  for (const type of ['mouseMoved', 'mousePressed', 'mouseReleased']) await cdp('Input.dispatchMouseEvent', { type, x: r.x, y: r.y, button: type === 'mouseMoved' ? 'none' : 'left', clickCount: type === 'mouseMoved' ? 0 : 1 });
  await sleep(20);
}
const CMD = 4;
const until = async (expr, ms = 5000) => { for (let t = 0; t < ms; t += 25) { if (await js(expr)) return true; await sleep(25); } return false; };

// Every internal link of every page, as served from where the site is published.
const pages = readdirSync(DIST, { recursive: true }).filter(file => String(file).endsWith('.html'));
const broken = new Set();
for (const page of pages) {
  const from = new URL(`${BASE}${String(page).replace(/index\.html$/, '')}`, ORIGIN);
  for (const [, link] of readFileSync(join(DIST, String(page)), 'utf8').matchAll(/\b(?:href|src)="([^"#]+)/g)) {
    const target = new URL(link, from);
    if (target.origin === ORIGIN && (await fetch(target)).status !== 200) broken.add(`${page}: ${link}`);
  }
}
check(`every internal link of ${pages.length} pages resolves`, pages.length > 5 && broken.size === 0, [...broken].slice(0, 5).join(', '));

await cdp('Runtime.enable'); await cdp('Log.enable'); await cdp('Network.enable'); await cdp('Page.enable');
await cdp('Emulation.setFocusEmulationEnabled', { enabled: true });
await cdp('Browser.grantPermissions', { origin: ORIGIN, permissions: ['clipboardReadWrite', 'clipboardSanitizedWrite'] });
await cdp('Browser.setDownloadBehavior', { behavior: 'allow', downloadPath: downloads });
await cdp('Emulation.setDeviceMetricsOverride', { width: 1280, height: 900, deviceScaleFactor: 1, mobile: false });
await cdp('Page.addScriptToEvaluateOnNewDocument', { source: `{
  const real = WebAssembly.instantiateStreaming;
  WebAssembly.instantiateStreaming = async (...args) => { const r = await real(...args); window.emdMemory = r.instance.exports.memory; return r; };
}` });
await cdp('Page.navigate', { url: `${ORIGIN}${BASE}keyboard/` });
check('page loads', await until(`document.readyState==='complete' && !!document.querySelector('#kb-source')`));
await sleep(500);

const map = await js(`Object.fromEntries([...document.querySelectorAll('.kb-key')].map(k=>[k.querySelector('kbd').textContent,k.dataset.insert]))`);
eq('eight keys', Object.keys(map), [...'asdfghjk']);
eq('eight glyphs', Object.values(map).map(g => g.codePointAt(0).toString(16)).sort(), ['2010', '2011', '2012', '2013', '2014', '2015', '2212', '2d']);
const CLI_ALPHABET = spawnSync(EMD, ['keys'], { input: 'asdfghjk', encoding: 'utf8' }).stdout.trim();
eq('page key table equals `emd keys`', Object.values(map).join(''), CLI_ALPHABET);

await click('#kb-source');
eq('click focuses the source', await js(`document.activeElement.id`), 'kb-source');
for (const k of 'asdfghjk') await key(k);
eq('typing asdfghjk writes the eight dashes', await value(), Object.values(map).join(''));
eq('count', await count(), '8 dashes · 1 line');
const decoded = spawnSync(EMD, ['check', '/dev/stdin'], { input: await value(), encoding: 'utf8' });
check('the page and the CLI both refuse this source', (await issues()).length > 0 && decoded.status !== 0, JSON.stringify(await issues()));

const before = await value();
for (const k of ['z', ' ', '1']) await key(k);
eq('z, space, 1 are rejected', await value(), before);
check('rejection is announced', (await status()).startsWith('Only the eight'), await status());

await key('Enter');
eq('Enter adds a newline', await value(), `${before}\n`);
eq('newline counts a line, not a dash', await count(), '8 dashes · 2 lines');
eq('feedback clears after a valid edit', await status(), '');
await key('Backspace');
eq('Backspace removes it', await value(), before);

await key('z', { modifiers: CMD, commands: ['undo'] });
eq('undo restores the newline', await value(), `${before}\n`);
await key('z', { modifiers: CMD | 8, commands: ['redo'] });
eq('redo removes it again', await value(), before);

await key('a', { modifiers: CMD, commands: ['selectAll'] });
await key('s');
eq('typing replaces a selection', await value(), map.s);

await click('#kb-clear');
eq('Clear empties', await value(), '');
eq('count after Clear', await count(), '0 dashes · 0 lines');
eq('table after Clear', await rows(), 0);

await click('.kb-key:nth-child(3)');
const third = await js(`document.querySelector('.kb-key:nth-child(3)').dataset.insert`);
eq('on-screen key inserts', await value(), third);
eq('on-screen key keeps focus in the source', await js(`document.activeElement.id`), 'kb-source');
await key('a', { modifiers: CMD, commands: ['undo'] });
await click('#kb-clear');

await click('#kb-source');
for (let i = 0; i < 40; i++) await key('a');
let lines = (await value()).split('\n').map(l => [...l].length);
eq('40 dashes wrap at 32', lines, [32, 8]);
eq('caret stays at the end', await caret(), (await value()).length);
await js(`document.querySelector('#kb-source').setSelectionRange(5,5)`);
await key('s');
const mid = await value();
eq('insert in the middle lands at the caret', [...mid][5], map.s);
eq('caret follows the inserted dash', await caret(), 6);
eq('a middle insert keeps the old break, so the overflow takes its own line', mid.split('\n').map(l => [...l].length), [32, 1, 8]);
for (let i = 0; i < 30; i++) await key('d');
eq('no line passes 32 after many middle inserts', Math.max(...(await value()).split('\n').map(l => [...l].length)), 32);
eq('wrap keeps every dash', [...(await value()).replaceAll('\n', '')].length, 71);
eq('count', await count(), `71 dashes · ${(await value()).split('\n').length} lines`);

const whole = await value();
await click('#kb-copy'); await sleep(100);
eq('Copy puts the source on the clipboard', await js(`navigator.clipboard.readText()`), whole);
await click('#kb-clear'); await click('#kb-source');
await key('v', { modifiers: CMD, commands: ['paste'] });
eq('paste of dashes is accepted', await value(), whole);
await js(`navigator.clipboard.writeText('hello')`);
await key('v', { modifiers: CMD, commands: ['paste'] });
eq('paste of anything else leaves the source', await value(), whole);
check('rejected paste is announced', (await status()).startsWith('Only the eight'), await status());
await js(`navigator.clipboard.writeText(${JSON.stringify(map.a + ' ' + map.a)})`);
await key('v', { modifiers: CMD, commands: ['paste'] });
eq('a mixed paste is rejected whole, not filtered', await value(), whole);

await click('#kb-clear'); await click('#kb-source');
await cdp('Input.insertText', { text: 'a' });
eq('text arriving without keydown is mapped, as on phones', await value(), map.a);
await cdp('Input.insertText', { text: 'q' });
eq('other text arriving without keydown is rejected', await value(), map.a);
await cdp('Input.imeSetComposition', { text: 'x', selectionStart: 1, selectionEnd: 1 });
await cdp('Input.insertText', { text: 'x' });
await sleep(30);
eq('IME composition cannot leave foreign text', await value(), map.a);

check('one dash reports a problem', (await issues()).length > 0, 'no problem listed');
await click('#kb-run'); await sleep(30);
const oneDash = await js(`({s:document.querySelector('#kb-status').textContent,hidden:document.querySelector('#kb-result').hidden})`);
check('run on a bad source shows a result, no crash', !oneDash.hidden && oneDash.s.length > 0, JSON.stringify(oneDash));
await click('#kb-clear');
await click('#kb-run'); await sleep(30);
check('running an empty source reports a fault', (await js(`document.querySelector('#kb-status').textContent`)).startsWith('fault'));

const examples = await js(`[...document.querySelectorAll('#kb-example option')].map(o=>({name:o.value,input:o.dataset.input??''}))`);
check('the page lists examples', examples.length > 0);
for (const { name, input } of examples) {
  await js(`(()=>{const s=document.querySelector('#kb-example');s.value=${JSON.stringify(name)};s.dispatchEvent(new Event('change'))})()`);
  const asm = await js(`document.querySelector('#kb-example-assembly').getAttribute('href')`);
  eq(`${name}: assembly link`, (await js(`fetch(${JSON.stringify(asm)}).then(r=>r.status)`)), 200);
  await click('#kb-load-example');
  await until(`!document.querySelector('#kb-load-example').disabled`);
  const file = readFileSync(`${DIST}/examples/${name}.emd`, 'utf8');
  eq(`${name}: loads the served file`, await value(), file);
  eq(`${name}: no problems`, await issues(), []);
  check(`${name}: decoded`, await rows() > 0, 'empty');
  check(`${name}: no line passes 32`, Math.max(...(await value()).split('\n').map(l => [...l].length)) <= 32);
  eq(`${name}: input field`, await js(`document.querySelector('#kb-input').value`), input);
  await click('#kb-run');
  await until(`!document.querySelector('#kb-result').hidden`);
  const got = await js(`document.querySelector('#kb-output').textContent`);
  const st = await js(`document.querySelector('#kb-status').textContent`);
  const cli = spawnSync(EMD, ['run', '--max-steps', '100000000', `${DIST}/examples/${name}.emd`], { input, encoding: 'utf8', timeout: 60000 });
  eq(`${name}: page output equals \`emd run\``, got, cli.stdout);
    check(`${name}: halts on the page`, /halt/i.test(st), st);
}

await click('#kb-download');
for (let i = 0; i < 80 && !readdirSync(downloads).some(f => f.endsWith('.emd')); i++) await sleep(50);
const saved = readdirSync(downloads);
check('Download saves program.emd', saved.includes('program.emd'), JSON.stringify(saved));
if (saved.includes('program.emd')) eq('Download has the exact bytes', readFileSync(`${downloads}/program.emd`, 'utf8'), await value());

await cdp('Emulation.setDeviceMetricsOverride', { width: 390, height: 844, deviceScaleFactor: 2, mobile: true });
await sleep(300);
eq('no sideways scroll on a phone', await js(`document.documentElement.scrollWidth <= window.innerWidth`), true);

// The page decodes on every keystroke, so memory must stop growing however long someone types.
const typeAndRun = times => js(`{
  const source = document.querySelector('#kb-source'), run = document.querySelector('#kb-run');
  for (let i = 0; i < ${times}; i++) { source.value = '-\\u2010'.repeat(500); source.dispatchEvent(new Event('input')); run.click(); }
}`);
await typeAndRun(500);
const settled = await js('window.emdMemory.buffer.byteLength');
await typeAndRun(3000);
eq('memory stops growing across 3000 decodes and runs', await js('window.emdMemory.buffer.byteLength'), settled);

eq('no console errors, exceptions or failed requests', problems, []);

console.log(`\n${passed} passed, ${failed} failed`);
ws.close(); chrome.kill(); server.close();
await sleep(300);
rmSync(work, { recursive: true, force: true });
process.exit(failed ? 1 : 0);
