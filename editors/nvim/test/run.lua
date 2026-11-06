-- Run through main.lua. Needs EMD_BIN pointing at the binary.
vim.cmd("filetype plugin on")
vim.cmd("runtime ftdetect/emd.lua")
vim.cmd("runtime plugin/emd.lua")
vim.o.mouse = "a"
vim.o.columns, vim.o.lines = 120, 40
vim.o.shortmess = vim.o.shortmess .. "F"
local emd = require("emd")
local failures = 0

local function check(name, ok, detail)
  if not ok then
    failures = failures + 1
    io.stderr:write("FAIL " .. name .. ": " .. tostring(detail) .. "\n")
  end
end

local function read(path)
  local f = assert(io.open(path, "rb"))
  local bytes = f:read("*a")
  f:close()
  return bytes
end

local function feed(keys) vim.api.nvim_feedkeys(vim.api.nvim_replace_termcodes(keys, true, false, true), "xt", false) end

local dir = vim.fn.tempname()
vim.fn.mkdir(dir)
local path = dir .. "/t.emd"

-- The instruction table against the real binary.
local letters = {}
for _, entry in ipairs(emd.instructions) do letters[#letters + 1] = entry[2] end
local typed = vim.system({ emd.cli, "keys" }, { stdin = table.concat(letters) }):wait()
check("keys", typed.code == 0, typed.stderr)
local all = dir .. "/all.emd"
local f = assert(io.open(all, "wb")); f:write(typed.stdout); f:close()
local listed = vim.split(vim.system({ emd.cli, "disasm", all }, { text = true }):wait().stdout, "\n", { trimempty = true })
check("32 instructions", #listed == 32 and #emd.instructions == 32, #listed)
for i, entry in ipairs(emd.instructions) do check("table " .. entry[1], listed[i] == entry[1], listed[i]) end

-- Typing letters, and the exact bytes on disk.
vim.cmd.edit(path)
check("filetype", vim.bo.filetype == "emd", vim.bo.filetype)
feed("iasaddagf<Esc>")
local program = "-\226\128\144-\226\128\145\226\128\145-\226\128\147\226\128\146"
check("letters type dashes", vim.api.nvim_get_current_line() == program, vim.api.nvim_get_current_line())
vim.cmd("silent write")
check("the file is what was typed", read(path) == program .. "\n", #read(path))
vim.cmd("edit!")
check("a final newline does not bother the buffer", vim.api.nvim_get_current_line() == program)

vim.api.nvim_buf_set_lines(0, 0, -1, false, { "-", "\226\128\144-", "\226\128\145" })
vim.cmd.EmdHints()
vim.wait(20, function() return false end)
local across = {}
for _, m in ipairs(vim.api.nvim_buf_get_extmarks(0, -1, 0, -1, { details = true })) do
  if m[4].virt_text then across[#across + 1] = vim.trim(m[4].virt_text[1][1]) end
end
check("a pair can cross a line", table.concat(across, ",") == "PUSH 1,PUSH 2", table.concat(across, ","))
vim.api.nvim_win_set_cursor(0, { 3, 0 })
check("describe across lines", emd.describe() == "1  PUSH 2  U+002D U+2011", emd.describe())
vim.cmd.EmdHints()
vim.cmd.EmdFmt()
check("EmdFmt rewraps", table.concat(vim.api.nvim_buf_get_lines(0, 0, -1, false), "|") == "-\226\128\144-\226\128\145", table.concat(vim.api.nvim_buf_get_lines(0, 0, -1, false), "|"))
vim.api.nvim_buf_set_lines(0, 0, -1, false, { program })
vim.cmd("silent write!")

-- Other letters stay letters, and the keys can be turned off.
feed("ccz<Esc>")
check("other letters pass", vim.api.nvim_get_current_line() == "z", vim.api.nvim_get_current_line())
vim.cmd.EmdKeys()
feed("cca<Esc>")
check("keys off", vim.api.nvim_get_current_line() == "a", vim.api.nvim_get_current_line())
vim.cmd.EmdKeys()
feed("cc<Esc>")

-- The keyboard, through real mouse events in a child Neovim with a UI attached:
-- without one, nothing drains the input queue.
vim.cmd.EmdKeyboard()
check("keyboard opens", emd.keyboard_open())
vim.cmd.EmdKeyboard()
check("keyboard closes", not emd.keyboard_open())

local child = vim.fn.jobstart({
  vim.v.progpath, "--embed", "--headless", "-n", "-u", "NONE", "-i", "NONE",
  "--cmd", "set rtp^=editors/nvim", "--cmd", "set mouse=a", "--cmd", "filetype plugin on",
  "--cmd", "runtime ftdetect/emd.lua", "--cmd", "runtime plugin/emd.lua",
}, { rpc = true })
local function rpc(method, ...) return vim.rpcrequest(child, method, ...) end
local function child_lua(code, ...) return rpc("nvim_exec_lua", code, { ... }) end
local function settle() vim.wait(120, function() return false end) end
rpc("nvim_ui_attach", 120, 40, {})
rpc("nvim_command", "edit " .. dir .. "/mouse.emd")
rpc("nvim_command", "EmdKeyboard")
settle()

local lines = child_lua([[
  for _, w in ipairs(vim.api.nvim_tabpage_list_wins(0)) do
    local c = vim.api.nvim_win_get_config(w)
    if c.relative ~= "" then
      local p = vim.api.nvim_win_get_position(w)
      return { lines = vim.api.nvim_buf_get_lines(vim.api.nvim_win_get_buf(w), 0, -1, false), row = p[1], col = p[2], border = 1 }
    end
  end
]])
check("float", lines ~= vim.NIL and lines.lines ~= nil, lines)

local function click_on(text, row)
  for l, line in ipairs(lines.lines) do
    local at = line:find(text, 1, true)
    if at and (not row or l == row) then
      -- Screen columns: a dash is one cell wide but three bytes.
      local screen = vim.fn.strdisplaywidth(line:sub(1, at - 1))
      local y, x = lines.row + lines.border + l - 1, lines.col + lines.border + screen
      rpc("nvim_input_mouse", "left", "press", "", 0, y, x)
      rpc("nvim_input_mouse", "left", "release", "", 0, y, x)
      settle()
      return
    end
  end
  check("cell " .. text, false, "not on the keyboard")
end

local source_win = rpc("nvim_get_current_win")
click_on("PUSH 1")
click_on("PUSH 2")
click_on("ADD")
click_on("HALT")
check("clicks keep focus", rpc("nvim_get_current_win") == source_win)
check("mouse: normal mode", rpc("nvim_get_current_line") == program, rpc("nvim_get_current_line"))
check("mouse: normal mode stays", rpc("nvim_get_mode").mode == "n", rpc("nvim_get_mode").mode)

rpc("nvim_buf_set_lines", 0, 0, -1, false, { "" })
rpc("nvim_input", "i")
settle()
click_on("a    ", 1)
click_on("s    ", 1)
click_on("-", 2)
check("mouse: insert mode stays", rpc("nvim_get_mode").mode == "i", rpc("nvim_get_mode").mode)
check("mouse: insert mode", rpc("nvim_get_current_line") == "-\226\128\144-", rpc("nvim_get_current_line"))
rpc("nvim_input", "<Esc>")
settle()

-- A click outside the keyboard is an ordinary click.
rpc("nvim_buf_set_lines", 0, 0, -1, false, { "abc", "def" })
rpc("nvim_input_mouse", "left", "press", "", 0, 1, 2)
rpc("nvim_input_mouse", "left", "release", "", 0, 1, 2)
settle()
-- The row only: the column comes out the same with or without the plugin's mappings.
check("ordinary click reaches the window", rpc("nvim_win_get_cursor", 0)[1] == 2, rpc("nvim_win_get_cursor", 0)[1])
check("ordinary click types nothing", table.concat(rpc("nvim_buf_get_lines", 0, 0, -1, false)) == "abcdef")
vim.fn.jobstop(child)

-- Diagnostics from the real doctor.
local function diagnostics_for(text_lines)
  vim.api.nvim_buf_set_lines(0, 0, -1, false, text_lines)
  local done = false
  emd.lint(0, function() done = true end)
  vim.wait(3000, function() return done end, 10)
  return vim.diagnostic.get(0)
end
local d = diagnostics_for({ program })
check("clean program", #d == 0, vim.inspect(d))
d = diagnostics_for({ "-\226\128\144x-" })
check("foreign code point", #d >= 1 and d[1].col == 4 and d[1].message:find("U+0078", 1, true), vim.inspect(d))
d = diagnostics_for({ "\226\136\146\226\136\146" })
check("unassigned pair", #d == 1 and d[1].message:find("unassigned", 1, true), vim.inspect(d))

-- Rainbow, hints, hover text.
vim.api.nvim_buf_set_lines(0, 0, -1, false, { program })
vim.wait(20, function() return false end)
vim.cmd.EmdHints()
local marks = vim.api.nvim_buf_get_extmarks(0, -1, 0, -1, { details = true })
local hints, colors = {}, {}
for _, m in ipairs(marks) do
  local details = m[4]
  if details.virt_text then hints[#hints + 1] = vim.trim(details.virt_text[1][1]) end
  if details.hl_group and tostring(details.hl_group):find("EmdRainbow") then colors[details.hl_group] = true end
end
check("hints name each instruction", table.concat(hints, ",") == "PUSH 1,PUSH 2,ADD,HALT", table.concat(hints, ","))
check("rainbow paints", next(colors) ~= nil)
vim.api.nvim_win_set_cursor(0, { 1, 8 })
check("describe", emd.describe() == "2  ADD  U+2011 U+002D", emd.describe())
vim.api.nvim_win_set_cursor(0, { 1, 0 })
check("describe first", emd.describe() == "0  PUSH 1  U+002D U+2010", emd.describe())

-- A report goes to a scratch window.
vim.bo.modified = false
vim.api.nvim_buf_set_lines(0, 0, -1, false, { program })
vim.cmd("write!")
vim.cmd.EmdDisasm()
check("report", vim.api.nvim_buf_get_lines(0, 0, 1, false)[1] == "PUSH 1", vim.api.nvim_buf_get_lines(0, 0, 1, false)[1])
vim.cmd.close()

-- The studio, driven like a user would: real keys in a child Neovim with a UI.
do
  local file = dir .. "/studio.emd"
  local handle = assert(io.open(file, "wb"))
  handle:write("-\226\128\144-\226\128\145\226\128\145-\226\128\145-\226\128\147\226\128\146")
  handle:close()
  local ch = vim.fn.jobstart({
    vim.v.progpath, "--embed", "--headless", "-n", "-u", "NONE", "-i", "NONE",
    "--cmd", "set rtp^=editors/nvim", "--cmd", "set mouse=a", "--cmd", "filetype plugin on",
    "--cmd", "runtime ftdetect/emd.lua", "--cmd", "runtime plugin/emd.lua",
  }, { rpc = true, env = { EMD_BIN = emd.cli } })
  local function r(method, ...)
    return vim.rpcrequest(ch, method, ...)
  end
  local function lua(code, ...) return r("nvim_exec_lua", code, { ... }) end
  r("nvim_ui_attach", 160, 50, {})
  -- A file that does not exist yet: the studio writes nothing until the user saves.
  local fresh = dir .. "/fresh.emd"
  r("nvim_command", "edit " .. fresh)
  -- Options a personal configuration may turn on must not reach the studio's windows.
  r("nvim_command", "set number relativenumber list signcolumn=yes")
  r("nvim_ui_try_resize", 120, 30)
  vim.wait(50)
  r("nvim_command", "EmdStudio")
  vim.wait(200)
  local hidden = lua([[
    local win, out = require("emd.studio").win.keyboard, {}
    local buf = vim.api.nvim_win_get_buf(win)
    for i, line in ipairs(vim.api.nvim_buf_get_lines(buf, 0, -1, false)) do
      local last = vim.fn.screenpos(win, i, math.max(#line, 1))
      if line ~= "" and (last.row == 0 or vim.fn.screenpos(win, i, 1).row ~= last.row) then out[#out + 1] = line end
    end
    return out
  ]])
  check("at 120x30 every key is on screen, none broken across lines", #hidden == 0, vim.inspect(hidden))
  local source_width = lua('return vim.api.nvim_win_get_width(require("emd.studio").source_win)')
  check("at 120x30 the source holds a full line", source_width >= 32, source_width)
  r("nvim_ui_try_resize", 80, 24)
  vim.wait(50)
  r("nvim_command", "tabclose")
  vim.wait(100)
  r("nvim_command", "EmdStudio")
  vim.wait(200)
  source_width = lua('return vim.api.nvim_win_get_width(require("emd.studio").source_win)')
  check("at 80x24 the source holds a full line", source_width >= 32, source_width)
  local source_height = lua('return vim.api.nvim_win_get_height(require("emd.studio").source_win)')
  check("at 80x24 the keyboard leaves room for the source", source_height >= 5, source_height)
  r("nvim_command", "tabclose")
  vim.wait(100)
  r("nvim_ui_try_resize", 160, 50)
  vim.wait(50)
  r("nvim_command", "EmdStudio")
  vim.wait(200)
  check("opening the studio does not save", vim.fn.filereadable(fresh) == 0, fresh)
  local gutters = lua([[
    local studio, out = require("emd.studio"), {}
    local wins = vim.deepcopy(studio.win)
    wins.source = studio.source_win
    for name, win in pairs(wins) do
      local list = vim.wo[win].list and name ~= "source"
      if vim.fn.getwininfo(win)[1].textoff ~= 0 or list then out[#out + 1] = name end
    end
    table.sort(out)
    return out
  ]])
  check("no studio window has a gutter or shows blanks", #gutters == 0, vim.inspect(gutters))
  r("nvim_command", "set nonumber norelativenumber nolist signcolumn=auto")
  r("nvim_input", "iasgf<Esc>:silent w<CR>")
  vim.wait(400)
  check("typing into it and saving", read(fresh) == "-\226\128\144\226\128\147\226\128\146\n", #read(fresh))
  -- Past 32 code points the line breaks by itself, here inside an instruction.
  r("nvim_command", "%delete _")
  r("nvim_input", "i" .. string.rep("as", 16) .. "a<Esc>")
  vim.wait(400)
  local wrapped = r("nvim_buf_get_lines", 0, 0, -1, false)
  check("the line breaks at the limit", #wrapped == 2 and vim.fn.strchars(wrapped[1]) == 32 and vim.fn.strchars(wrapped[2]) == 1, vim.inspect(wrapped))
  check("the cursor follows the break", r("nvim_win_get_cursor", 0)[1] == 2)
  r("nvim_command", "silent write")
  r("nvim_command", "tabclose")
  vim.wait(100)
  check("closing the tab ends the studio", lua('return require("emd.studio").source_win') == vim.NIL)
  r("nvim_input", "ox<Esc>u")
  vim.wait(100)
  check("no prompt left behind", r("nvim_get_mode").blocking == false, r("nvim_get_mode"))
  r("nvim_command", "edit " .. file)
  r("nvim_command", "EmdStudio")
  local function panel(name)
    return lua('return vim.api.nvim_buf_get_lines(require("emd.studio").buf[...], 0, -1, false)', name)
  end
  local function until_true(what, test)
    local ok = vim.wait(3000, test, 20)
    check(what, ok, what)
  end
  local function state() return lua('return require("emd.studio").state') end
  until_true("debugger starts", function() local s = state(); return s ~= vim.NIL and s.step == 0 end)
  check("listing", panel("listing")[3] == "    2  ADD", panel("listing")[3])
  check("analysis names faults", table.concat(panel("analysis"), "\n"):find("no stack underflow", 1, true) ~= nil)
  r("nvim_input", "<F10><F10>")
  until_true("F10 steps", function() return state().step == 2 end)
  check("stack panel, top first", panel("stack")[1] == "top 2" and panel("stack")[2] == "    1", vim.inspect(panel("stack")))
  r("nvim_input", "<F8>")
  until_true("F8 goes back", function() return state().step == 1 end)
  check("back restores the stack", panel("stack")[1] == "top 1", vim.inspect(panel("stack")))
  r("nvim_input", "<F5>")
  until_true("F5 runs to the fault", function() return state().status:find("underflow", 1, true) ~= nil end)
  check("the meter counts it", table.concat(panel("damage"), "\n"):find("faults survived       1", 1, true) ~= nil, table.concat(panel("damage"), "|"))
  check("the meter draws eight bars", #panel("damage") >= 13)
  local bar = lua("return vim.wo[require('emd.studio').source_win].winbar")
  check("the winbar says what happened", bar:find("stack underflow", 1, true) ~= nil, bar)
  r("nvim_input", "<F7>")
  until_true("F7 restarts", function() return state().step == 0 end)
  r("nvim_command", "EmdInput x")
  vim.fn.jobstop(ch)
end

vim.fn.delete(dir, "rf")
if failures > 0 then
  io.stderr:write(failures .. " failure(s)\n")
  vim.cmd("cquit 1")
else
  io.stdout:write("nvim plugin ok\n")
  vim.cmd("qall!")
end
