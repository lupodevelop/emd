#!/usr/bin/env python3
"""The Neovim studio through a real pseudo-terminal: the bytes a terminal sends for F keys, clicks and the wheel.

    editors/nvim/test/terminal.py [plain|personal] [rows] [columns]

`plain` starts Neovim with no configuration. `personal` uses a throwaway copy of the
user's configuration and plugins, so nothing of the real ones can change. POSIX only.
"""
import fcntl, json, os, pty, re, select, shutil, struct, subprocess, sys, tempfile, termios, threading, time

REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../..'))
MODE = sys.argv[1] if len(sys.argv) > 1 else "plain"
W = tempfile.mkdtemp(prefix="emd-studio-")
SOCK = "./s"  # relative: a socket path past 104 bytes fails on macOS
EMD = os.environ.get("EMD_BIN") or shutil.which("emd")
SOURCE = subprocess.run([EMD, "keys"], input="asaddagf", capture_output=True, text=True).stdout.strip()
PATH = f"{W}/t.emd"
open(PATH, "w").write(SOURCE + "\n")
ROWS, COLS = int(sys.argv[2]) if len(sys.argv) > 2 else 45, int(sys.argv[3]) if len(sys.argv) > 3 else 140

env = dict(os.environ, TERM="xterm-256color", COLORTERM="truecolor", EMD_BIN=EMD)
args = ["nvim", "--listen", SOCK, "-n", "-i", "NONE"]
if MODE == "plain":
    args += ["-u", "NONE", "--cmd", f"set rtp^={REPO}/editors/nvim mouse=a", "--cmd", "filetype plugin on", "--cmd", "runtime plugin/emd.lua"]
else:
    os.makedirs(f"{W}/config"); os.makedirs(f"{W}/data")
    home = os.path.expanduser("~")
    subprocess.check_call(["cp", "-cR" if sys.platform == "darwin" else "-R", f"{home}/.config/nvim", f"{W}/config/nvim"])
    subprocess.check_call(["cp", "-cR" if sys.platform == "darwin" else "-R", f"{home}/.local/share/nvim", f"{W}/data/nvim"])
    env.update(XDG_CONFIG_HOME=f"{W}/config", XDG_DATA_HOME=f"{W}/data", XDG_STATE_HOME=f"{W}/state", XDG_CACHE_HOME=f"{W}/cache")
args.append(PATH)

pid, fd = pty.fork()
if pid == 0:
    os.chdir(W)
    os.execvpe("nvim", args, env)
fcntl.ioctl(fd, termios.TIOCSWINSZ, struct.pack("HHHH", ROWS, COLS, 0, 0))
log = open(f"{W}/tty.log", "wb")
stop = False
def pump():
    while not stop:
        r, _, _ = select.select([fd], [], [], 0.1)
        if r:
            try:
                data = os.read(fd, 65536)
            except OSError:
                return
            if not data:
                return
            log.write(data)
threading.Thread(target=pump, daemon=True).start()

def send(b):
    os.write(fd, b if isinstance(b, bytes) else b.encode())

def lua(expr):
    code = f"luaeval({json.dumps('vim.json.encode((function() ' + expr + ' end)())')})"
    r = subprocess.run(["nvim", "--server", SOCK, "--remote-expr", code], capture_output=True, text=True, timeout=20, env=env, cwd=W)
    if r.returncode != 0 or not r.stdout.strip():
        raise RuntimeError(f"{expr}: {r.stderr or r.stdout}")
    return json.loads(r.stdout)

def until(expr, seconds=8):
    end = time.time() + seconds
    last = None
    while time.time() < end:
        try:
            last = lua(f"return {expr}")
            if last is True:
                return True
        except Exception as e:
            last = str(e)
        time.sleep(0.05)
    return last

passed = failed = 0
def check(name, good, detail=""):
    global passed, failed
    passed += bool(good); failed += not good
    print(("ok   " if good else "FAIL ") + name + ("" if good else f" :: {detail}"), flush=True)
def wait(name, expr, seconds=8):
    got = until(expr, seconds)
    check(name, got is True, f"{expr} -> {got}")

F = {4: b"\x1bOS", 5: b"\x1b[15~", 6: b"\x1b[17~", 7: b"\x1b[18~", 8: b"\x1b[19~", 9: b"\x1b[20~", 10: b"\x1b[21~"}
def click(row, col):  # 0-based screen cell, SGR encoding as terminals send with mouse=a
    send(f"\x1b[<0;{col+1};{row+1}M".encode()); time.sleep(0.03)
    send(f"\x1b[<0;{col+1};{row+1}m".encode()); time.sleep(0.1)

def screen():
    return lua(f"local out = {{}} for r = 1, {ROWS} do local l = {{}} for c = 1, {COLS} do l[#l+1] = vim.fn.screenstring(r, c) end out[#out+1] = table.concat(l) end return out")

STATE = "require('emd.studio').state"
step = lambda n: f"{STATE} ~= nil and {STATE}.step == {n}"
source_text = "vim.api.nvim_buf_get_lines(require('emd.studio').source_buf, 0, -1, false)[1]"

wait("nvim starts and detects the filetype", "vim.v.vim_did_enter == 1 and vim.bo.filetype == 'emd'", 40)
if MODE != "plain":
    time.sleep(2)
send(":EmdStudio\r")
wait("studio opens from typed :EmdStudio", step(0))
wait("focus sits in the source", "vim.api.nvim_get_current_win() == require('emd.studio').source_win")

send(F[10]); wait("F10 steps", step(1))
send(F[8]); wait("F8 steps back", step(0))
send(F[5]); wait("F5 continues to the end", step(4))
send(F[7]); wait("F7 goes to the start", step(0))
send(F[5]); wait("F5 again", step(4))
send(F[6]); time.sleep(0.3)
check("F6 with no breakpoint stays put, as documented", lua(f"return {step(4)}"))
send(F[7]); wait("back to the start", step(0))
send("\r"); wait("Enter steps in normal mode", step(1))
send("\x7f"); wait("Backspace steps back in normal mode", step(0))
send("0ll"); time.sleep(0.2)
send(F[9])
wait("F9 sets a breakpoint on the instruction under the cursor", f"vim.deep_equal({STATE}.breaks, {{ 1 }})")
send(F[5]); wait("F5 stops at it", step(1))
send(F[5]); wait("F5 goes on to the end", step(4))
send(F[6]); wait("F6 returns to the breakpoint", step(1))
send(F[9])
wait("F9 removes it", f"#{STATE}.breaks == 0")
send(F[7]); wait("back to the start again", step(0))
send(F[4])
wait("F4 plays to the end", step(4), 10)
wait("play stops itself", "require('emd.studio').timer == nil", 5)
send(F[7]); wait("back to the start", step(0))

kb = "require('emd.studio').win.keyboard"
kb_lines = lua(f"return vim.api.nvim_buf_get_lines(vim.api.nvim_win_get_buf({kb}), 0, -1, false)")
check("the keyboard has no gutter", lua(f"return vim.fn.getwininfo({kb})[1].textoff") == 0)
def cell(line, byte):  # 0-based screen cell of a byte of the keyboard buffer, as Neovim draws it
    p = lua(f"return vim.fn.screenpos({kb}, {line + 1}, {byte + 1})")
    return p["row"] - 1, p["col"] - 1
cells = []
glyph_of = lambda text: subprocess.run([EMD, "keys"], input=text, capture_output=True, text=True).stdout.strip()
letters = {glyph_of(l): l for l in "asdfghjk"}
for i, l in enumerate(kb_lines):
    if re.fullmatch(r" [asdfghjk](?: +[asdfghjk])*\s*", l):
        for m in re.finditer(r"[asdfghjk]", l):
            cells.append((i, len(l[:m.start()].encode()), m.group(0)))
    elif l.strip() and l.strip()[0] in letters:
        for m in re.finditer("|".join(map(re.escape, letters)), l):
            cells.append((i, len(l[:m.start()].encode()), letters[m.group(0)]))
    else:
        for m in re.finditer(r"[A-Z]+(?: \d)? ([asdfghjk]{2})", l):
            cells.append((i, len(l[:m.start()].encode()), m.group(1)))
check("the keyboard has 8 + 8 + 32 cells", len(cells) == 48, len(cells))
whole = "table.concat(vim.api.nvim_buf_get_lines(require('emd.studio').source_buf, 0, -1, false))"
before = lua(f"return {source_text}")
typed = before
sequence = ""
misses = []
for line, byte, text in cells:
    row, col = cell(line, byte)
    if row < 0:
        p = lua(f"local p = vim.api.nvim_win_get_position({kb}) return {{ p[1] + 2, p[2] + 2 }}")
        for button in (65, 64):
            for _ in range(len(kb_lines)):
                send(f"\x1b[<{button};{p[1]+1};{p[0]+1}M".encode()); time.sleep(0.05)
                row, col = cell(line, byte)
                if row >= 0:
                    break
            if row >= 0:
                break
    if row < 0 or col < 0:
        misses.append(f"{text}: not on screen"); continue
    click(row, col)
    want = glyph_of(text)
    sequence += want
    now = lua(f"return {whole}")
    # In normal mode a click types after the cursor, which ends on the last dash typed.
    if len(now) != len(before) + len(sequence) or sequence not in now:
        misses.append(f"{text}: {now!r} lacks {sequence!r}")
check("the line limit held while clicking", lua("local m = 0 for _, l in ipairs(vim.api.nvim_buf_get_lines(require('emd.studio').source_buf, 0, -1, false)) do m = math.max(m, vim.fn.strchars(l)) end return m") <= 32)
check("every cell on the keyboard types what it shows, at its drawn position", not misses, misses[:4])
check("the clicks leave focus in the source", lua("return vim.api.nvim_get_current_win() == require('emd.studio').source_win"))
check("the clicks leave normal mode", lua("return vim.api.nvim_get_mode().mode") == "n")
check("the edit is unsaved", lua("return vim.bo[require('emd.studio').source_buf].modified"))
check("the file on disk is untouched", open(PATH).read().strip() == SOURCE)
send(":silent! earlier 1f\r"); time.sleep(0.3)
lua(f"vim.api.nvim_buf_set_lines(require('emd.studio').source_buf, 0, -1, false, {{ [[{before}]] }}) return true")
time.sleep(0.2)
h_line = next(i for i, l in enumerate(kb_lines) if re.fullmatch(r" [asdfghjk](?: +[asdfghjk])*\s*", l) and "h" in l)
want = glyph_of("h")
lua(f"vim.api.nvim_win_call({kb}, function() vim.fn.winrestview({{ topline = {h_line + 1} }}) end) return true"); time.sleep(0.1)
row, col = cell(h_line, kb_lines[h_line].index("h"))
click(row, col); time.sleep(0.2)
after = lua(f"return {source_text}")
check("a click on key h types its dash", len(after) == len(before) + 1 and want in after, f"{before!r} -> {after!r}")
send("u"); time.sleep(0.3)
check("undo removes it", lua(f"return {source_text}") == before, lua(f"return {source_text}"))

send("A"); time.sleep(0.2)
check("A enters insert mode", lua("return vim.api.nvim_get_mode().mode").startswith("i"))
click(row, col); time.sleep(0.2)
check("a click in insert mode types and stays in insert mode", lua("return vim.api.nvim_get_mode().mode").startswith("i") and lua(f"return {source_text}") == before + want, lua(f"return {source_text}"))
send("a"); time.sleep(0.2)
a = subprocess.run([EMD, "keys"], input="a", capture_output=True, text=True).stdout.strip()
check("a typed key writes its dash in insert mode", lua(f"return {source_text}") == before + want + a, lua(f"return {source_text}"))
send(F[10]); time.sleep(0.4)
check("F10 works from insert mode too", lua("return vim.api.nvim_get_mode().mode").startswith("i"))
send("\x1b"); time.sleep(0.2)
send("uu"); time.sleep(0.3)

# A click on the source moves the cursor and types nothing.
geo = lua("local s = require('emd.studio') local p = vim.api.nvim_win_get_position(s.source_win) local i = vim.fn.getwininfo(s.source_win)[1] return { p[1], p[2], i.textoff, i.winbar }")
text_before = lua(f"return {source_text}")
click(geo[0] + geo[3], geo[1] + geo[2] + 2); time.sleep(0.2)
check("a click on the source only moves the cursor", lua("return vim.api.nvim_win_get_cursor(0)[2]") > 0 and lua(f"return {source_text}") == text_before, str(lua("return vim.api.nvim_win_get_cursor(0)")))

open(f"{W}/screen.txt", "w").write("\n".join(screen()))
errors = lua("return vim.split(vim.api.nvim_exec2('messages', { output = true }).output, '\\n')")
bad = [m for m in errors if "E5" in m or "rror" in m or "stack traceback" in m]
check("no errors in :messages", not bad, bad[:5])

send("\x1b"); time.sleep(0.2); send(":qa!\r")
for _ in range(100):
    done, status = os.waitpid(pid, os.WNOHANG)
    if done:
        break
    time.sleep(0.05)
else:
    os.kill(pid, 9); status = -1
stop = True
check("nvim quits cleanly", status == 0, status)
print(f"\n{MODE} {ROWS}x{COLS}: {passed} passed, {failed} failed; last screen in {W}/screen.txt")
sys.exit(1 if failed else 0)
