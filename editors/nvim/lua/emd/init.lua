-- emd for Neovim. The rules of the language stay in the `emd` binary, which
-- produces the diagnostics. This file holds only the two tables needed to type
-- and read dashes; crates/emd-core/tests/docs.rs checks them against the Rust.
local M = {}

M.cli = vim.env.EMD_BIN or "emd"
M.line_max = 32

-- Letters, in alphabet order. The dashes are spelled as numbers on purpose: a wrong
-- dash in this file could not be seen.
M.keys = "asdfghjk"
M.codes = { 0x2D, 0x2010, 0x2011, 0x2012, 0x2013, 0x2014, 0x2015, 0x2212 }

-- Each instruction and the two letters that type it.
M.instructions = {
  { "PUSH 0", "aa" }, { "PUSH 1", "as" }, { "PUSH 2", "ad" }, { "PUSH 3", "af" },
  { "PUSH 4", "ag" }, { "PUSH 5", "ah" }, { "PUSH 6", "aj" }, { "PUSH 7", "ak" },
  { "DUP", "sa" }, { "DROP", "ss" }, { "SWAP", "sd" }, { "OVER", "sf" }, { "ROT", "sg" },
  { "ADD", "da" }, { "SUB", "ds" }, { "MUL", "dd" }, { "DIV", "df" }, { "MOD", "dg" },
  { "LOAD", "fa" }, { "STORE", "fs" },
  { "JMP", "ga" }, { "JZ", "gs" }, { "JNZ", "gd" }, { "HALT", "gf" }, { "CALL", "gg" }, { "RET", "gh" },
  { "READ", "ha" }, { "WRITE", "hs" },
  { "EQ", "ja" }, { "LT", "js" }, { "GT", "jd" }, { "NOT", "jf" },
}

-- One row of the keyboard per family; 8 is the PUSH row, split for width.
local ROWS = { { 1, 8 }, { 9, 13 }, { 14, 18 }, { 19, 20 }, { 21, 26 }, { 27, 28 }, { 29, 32 } }

local function glyph(index) return vim.fn.nr2char(M.codes[index]) end

local function glyphs_of(letters)
  return (letters:gsub(".", function(k) return glyph(M.keys:find(k, 1, true)) end))
end

local mnemonic_of = {}
for _, entry in ipairs(M.instructions) do mnemonic_of[glyphs_of(entry[2])] = entry[1] end

local ns = {
  rainbow = vim.api.nvim_create_namespace("emd.rainbow"),
  hints = vim.api.nvim_create_namespace("emd.hints"),
  diagnostics = vim.api.nvim_create_namespace("emd.diagnostics"),
  keyboard = vim.api.nvim_create_namespace("emd.keyboard"),
}

local RAINBOW = { { "#e06c75", 1 }, { "#e5c07b", 3 }, { "#98c379", 2 }, { "#56b6c2", 6 }, { "#61afef", 4 }, { "#c678dd", 5 } }

local function define_highlights()
  for i, color in ipairs(RAINBOW) do
    vim.api.nvim_set_hl(0, "EmdRainbow" .. i, { fg = color[1], ctermfg = color[2], default = true })
  end
  vim.api.nvim_set_hl(0, "EmdHint", { link = "Comment", default = true })
  vim.api.nvim_set_hl(0, "EmdKey", { link = "Special", default = true })
end

local state = {} -- per buffer: { keys = bool, hints = bool, rainbow = bool, timer = timer }
local keyboard = { win = nil, buf = nil, cells = {}, source = nil }

-- Every code point of the buffer: { char, line, start byte, end byte }, newlines as code points too.
local function code_points(buf)
  local points = {}
  local lines = vim.api.nvim_buf_get_lines(buf, 0, -1, false)
  for l, line in ipairs(lines) do
    local col = 0
    for char in line:gmatch("[%z\1-\127\192-\255][\128-\191]*") do
      points[#points + 1] = { char = char, line = l - 1, from = col, to = col + #char }
      col = col + #char
    end
    if l < #lines then
      points[#points + 1] = { char = "\n", line = l - 1, from = col, to = col }
    end
  end
  return points
end

M.code_points = code_points

-- The code points that count as program: newlines go before decoding.
function M.dashes(points)
  local out = {}
  for _, p in ipairs(points) do
    if p.char ~= "\n" then out[#out + 1] = p end
  end
  return out
end

local function buffer_text(buf)
  return table.concat(vim.api.nvim_buf_get_lines(buf, 0, -1, false), "\n")
end

local function paint(buf)
  local s = state[buf]
  if not s then return end
  vim.api.nvim_buf_clear_namespace(buf, ns.rainbow, 0, -1)
  vim.api.nvim_buf_clear_namespace(buf, ns.hints, 0, -1)
  local dashes = M.dashes(code_points(buf))
  for i, p in ipairs(dashes) do
    if s.rainbow then
      local band = (p.line + (s.offset or 0)) % #RAINBOW + 1
      vim.api.nvim_buf_set_extmark(buf, ns.rainbow, p.line, p.from, { end_col = p.to, hl_group = "EmdRainbow" .. band })
    end
    if s.hints and i % 2 == 0 then
      local name = mnemonic_of[dashes[i - 1].char .. p.char]
      if name then
        vim.api.nvim_buf_set_extmark(buf, ns.hints, p.line, p.to, {
          virt_text = { { " " .. name .. " ", "EmdHint" } },
          virt_text_pos = "inline",
        })
      end
    end
  end
end

-- `emd doctor` names problems by code point or instruction: turn those into positions.
local function parse_doctor(text, points)
  local dashes = M.dashes(points)
  local found = {}
  local function add(p, message)
    p = p or points[#points] or { line = 0, from = 0, to = 0 }
    found[#found + 1] = {
      lnum = p.line, col = p.from, end_lnum = p.line, end_col = math.max(p.to, p.from + 1),
      severity = vim.diagnostic.severity.ERROR, source = "emd", message = message,
    }
  end
  for line in text:gmatch("[^\n]+") do
    local problem = line:match("^%s*%- (.+)$")
    if problem then
      local point = problem:match("^code point (%d+):")
      local instruction = problem:match("^instruction (%d+):")
      local long = problem:match("^line (%d+) has")
      if point then add(points[tonumber(point) + 1], problem)
      elseif instruction then add(dashes[tonumber(instruction) * 2 + 1], problem)
      elseif long then add({ line = tonumber(long) - 1, from = 0, to = 1 }, problem)
      else add(nil, problem) end
    end
  end
  return found
end

local warned = false

function M.lint(buf, done)
  local tmp = vim.fn.tempname() .. ".emd"
  local file = assert(io.open(tmp, "wb"))
  file:write(buffer_text(buf))
  file:close()
  local points = code_points(buf)
  local ok, err = pcall(vim.system, { M.cli, "doctor", tmp }, { text = true }, function(result)
    vim.schedule(function()
      os.remove(tmp)
      if vim.api.nvim_buf_is_valid(buf) then
        vim.diagnostic.set(ns.diagnostics, buf, parse_doctor(result.stdout or "", points))
      end
      if done then done() end
    end)
  end)
  if not ok then
    os.remove(tmp)
    if not warned then
      warned = true
      vim.notify("emd: cannot run `" .. M.cli .. "`, no diagnostics: " .. tostring(err), vim.log.levels.WARN)
    end
    if done then done() end
  end
end

-- Past the limit the line breaks by itself, even inside an instruction.
local function wrap_cursor_line(buf)
  if vim.api.nvim_get_current_buf() ~= buf then return end
  local row, col = unpack(vim.api.nvim_win_get_cursor(0))
  local line = vim.api.nvim_buf_get_lines(buf, row - 1, row, false)[1] or ""
  if vim.fn.strchars(line) <= M.line_max then return end
  local cut = vim.fn.byteidx(line, M.line_max)
  vim.api.nvim_buf_set_text(buf, row - 1, cut, row - 1, cut, { "", "" })
  if col >= cut then vim.api.nvim_win_set_cursor(0, { row + 1, col - cut }) end
end

-- The canonical layout: lines of the full width. Anything but dashes stays where it is,
-- for the diagnostics to find.
function M.format(buf)
  buf = buf or vim.api.nvim_get_current_buf()
  local chars = {}
  for _, p in ipairs(code_points(buf)) do
    if p.char ~= "\n" then chars[#chars + 1] = p.char end
  end
  local lines = {}
  for i = 1, #chars, M.line_max do
    lines[#lines + 1] = table.concat(chars, "", i, math.min(i + M.line_max - 1, #chars))
  end
  vim.api.nvim_buf_set_lines(buf, 0, -1, false, #lines > 0 and lines or { "" })
end

local function changed(buf)
  wrap_cursor_line(buf)
  paint(buf)
  local s = state[buf]
  if not s then return end
  if s.timer then s.timer:stop() end
  s.timer = vim.defer_fn(function()
    if vim.api.nvim_buf_is_valid(buf) then M.lint(buf) end
  end, 150)
end

local function set_keys(buf, on)
  state[buf].keys = on
  for i = 1, #M.keys do
    local letter = M.keys:sub(i, i)
    if on then
      vim.keymap.set("i", letter, glyph(i), { buffer = buf, desc = "emd: U+" .. string.format("%04X", M.codes[i]) })
    else
      pcall(vim.keymap.del, "i", letter, { buffer = buf })
    end
  end
end

-- In insert mode text goes at the cursor. In normal mode the cursor sits on a
-- character and cannot rest past the last one, so text goes after it, like `a`.
local function insert_at_cursor(win, text)
  local buf = vim.api.nvim_win_get_buf(win)
  local row, col = unpack(vim.api.nvim_win_get_cursor(win))
  local insert_mode = vim.api.nvim_get_mode().mode:sub(1, 1) == "i"
  local line = vim.api.nvim_buf_get_lines(buf, row - 1, row, false)[1] or ""
  local at = col
  if not insert_mode and #line > 0 then
    at = col + #(line:sub(col + 1):match("^[%z\1-\127\192-\255][\128-\191]*") or "")
  end
  vim.api.nvim_buf_set_text(buf, row - 1, at, row - 1, at, { text })
  local last_char = insert_mode and #text or #text - #(text:match("[%z\1-\127\192-\255][\128-\191]*$") or "")
  vim.api.nvim_win_set_cursor(win, { row, at + last_char })
end

local function cell_at(line, col)
  for _, cell in ipairs(keyboard.cells) do
    if cell.line == line and col >= cell.from and col < cell.to then return cell end
  end
end

-- What the keyboard types at a position of its own buffer (0-based line and byte).
function M.press(line, col)
  local cell = cell_at(line, col)
  local source = keyboard.source
  if not cell or not source or not vim.api.nvim_win_is_valid(source) then return nil end
  insert_at_cursor(source, cell.text)
  return cell.text
end

-- Lines never pass `width`: a wrapped key would hide the rows under it and cut a cell in two.
local function render_keyboard(width)
  local lines, cells = {}, {}
  local function add_cell(parts, text, shown, line)
    local from = #table.concat(parts)
    parts[#parts + 1] = shown
    cells[#cells + 1] = { line = line, from = from, to = from + #shown, text = text }
    parts[#parts + 1] = "  "
  end
  local per_line = math.max(1, math.min(#M.keys, math.floor((width - 1) / 7)))
  for first = 1, #M.keys, per_line do
    local keys_line, dashes, codes = { " " }, { " " }, { " " }
    for i = first, math.min(first + per_line - 1, #M.keys) do
      add_cell(keys_line, glyph(i), M.keys:sub(i, i) .. "    ", #lines)
      add_cell(dashes, glyph(i), glyph(i) .. "    ", #lines + 1)
      codes[#codes + 1] = string.format("%04X ", M.codes[i])
      codes[#codes + 1] = " "
    end
    lines[#lines + 1] = table.concat(keys_line)
    lines[#lines + 1] = table.concat(dashes)
    lines[#lines + 1] = table.concat(codes)
  end
  lines[#lines + 1] = ""
  for _, row in ipairs(ROWS) do
    local parts = { " " }
    for i = row[1], row[2] do
      local entry = M.instructions[i]
      local shown = entry[1] .. " " .. entry[2]
      if #parts > 1 and #table.concat(parts) + #shown > width then
        lines[#lines + 1] = table.concat(parts)
        parts = { " " }
      end
      add_cell(parts, glyphs_of(entry[2]), shown, #lines)
    end
    lines[#lines + 1] = table.concat(parts)
  end
  keyboard.cells = cells
  return lines
end

function M.keyboard_open() return keyboard.win ~= nil and vim.api.nvim_win_is_valid(keyboard.win) end

local function close_keyboard()
  if M.keyboard_open() then vim.api.nvim_win_close(keyboard.win, true) end
  keyboard.win = nil
end

-- `split`, if given, opens the keyboard as a window below it instead of a float.
function M.open_keyboard(split)
  if M.keyboard_open() then return end
  keyboard.source = vim.api.nvim_get_current_win()
  keyboard.buf = vim.api.nvim_create_buf(false, true)
  local lines = render_keyboard(split and vim.api.nvim_win_get_width(split) or vim.o.columns - 3)
  vim.api.nvim_buf_set_lines(keyboard.buf, 0, -1, false, lines)
  vim.bo[keyboard.buf].modifiable = false
  vim.bo[keyboard.buf].filetype = "emdkeyboard"
  for _, cell in ipairs(keyboard.cells) do
    vim.api.nvim_buf_set_extmark(keyboard.buf, ns.keyboard, cell.line, cell.from, { end_col = cell.to, hl_group = "EmdKey" })
  end
  if split then
    -- One more line: the studio gives this window a title bar. On a short terminal
    -- the source keeps five lines and the mouse wheel scrolls the keyboard.
    local height = math.min(#lines + 1, math.max(1, vim.api.nvim_win_get_height(split) - 6))
    keyboard.win = vim.api.nvim_open_win(keyboard.buf, false, { split = "below", win = split, height = height })
    return keyboard.win
  end
  local width = 0
  for _, line in ipairs(lines) do width = math.max(width, vim.fn.strdisplaywidth(line)) end
  keyboard.win = vim.api.nvim_open_win(keyboard.buf, false, {
    relative = "editor", anchor = "NE", row = 1, col = vim.o.columns, width = width + 1, height = #lines,
    style = "minimal", border = "rounded", title = " emd ", focusable = true,
  })
  if vim.o.mouse == "" then vim.notify("emd: set 'mouse' to a to click the keyboard", vim.log.levels.INFO) end
  return keyboard.win
end

function M.toggle_keyboard()
  if M.keyboard_open() then
    close_keyboard()
  else
    M.open_keyboard()
  end
end

-- A click on the keyboard types and leaves focus and mode alone. A click elsewhere is an ordinary click.
local function map_mouse(buf)
  for _, key in ipairs({ "<LeftMouse>", "<LeftRelease>", "<2-LeftMouse>" }) do
    vim.keymap.set({ "n", "i" }, key, function()
      local pos = vim.fn.getmousepos()
      if not (M.keyboard_open() and pos.winid == keyboard.win) then return key end
      if key ~= "<LeftRelease>" then
        keyboard.source = vim.api.nvim_get_current_win()
        -- Mappings with `expr` cannot edit a buffer: the edit waits for them to finish.
        vim.schedule(function() M.press(pos.line - 1, pos.column - 1) end)
      end
      return ""
    end, { buffer = buf, expr = true, replace_keycodes = true })
  end
end

function M.toggle_keys()
  local buf = vim.api.nvim_get_current_buf()
  if state[buf] then set_keys(buf, not state[buf].keys) end
end

function M.toggle_hints()
  local buf = vim.api.nvim_get_current_buf()
  if state[buf] then state[buf].hints = not state[buf].hints; paint(buf) end
end

function M.toggle_rainbow()
  local buf = vim.api.nvim_get_current_buf()
  if state[buf] then state[buf].rainbow = not state[buf].rainbow; paint(buf) end
end

function M.set_rainbow_offset(buf, offset)
  if state[buf] then
    state[buf].offset = offset
    paint(buf)
  end
end

-- The instruction under the cursor: index, mnemonic and code points.
function M.describe()
  local buf = vim.api.nvim_get_current_buf()
  local row, col = unpack(vim.api.nvim_win_get_cursor(0))
  local dashes = M.dashes(code_points(buf))
  for i, p in ipairs(dashes) do
    if p.line == row - 1 and col >= p.from and col < p.to then
      local index = math.floor((i - 1) / 2)
      local first, second = dashes[index * 2 + 1], dashes[index * 2 + 2]
      local name = second and mnemonic_of[first.char .. second.char] or "not an instruction"
      local code = function(q) return q and string.format("U+%04X", vim.fn.char2nr(q.char)) or "" end
      return string.format("%d  %s  %s %s", index, name, code(first), code(second))
    end
  end
  return ""
end

function M.hover()
  local text = M.describe()
  if text ~= "" then vim.lsp.util.open_floating_preview({ text }, "text", { border = "rounded" }) end
end

local function saved_file()
  if vim.bo.modified or vim.fn.filereadable(vim.api.nvim_buf_get_name(0)) == 0 then vim.cmd("silent write") end
  return vim.api.nvim_buf_get_name(0)
end

function M.terminal(tool)
  local file = saved_file()
  vim.cmd("botright split")
  vim.cmd.terminal(vim.fn.shellescape(M.cli) .. " " .. tool .. " " .. vim.fn.shellescape(file))
  vim.cmd.startinsert()
end

function M.report(tool)
  local file = saved_file()
  local result = vim.system({ M.cli, tool, file }, { text = true }):wait()
  vim.cmd("botright new")
  vim.bo.buftype, vim.bo.bufhidden, vim.bo.swapfile = "nofile", "wipe", false
  local text = (result.stdout or "") .. (result.stderr or "")
  vim.api.nvim_buf_set_lines(0, 0, -1, false, vim.split(text, "\n", { trimempty = true }))
  vim.bo.modifiable = false
end

function M.attach(buf)
  if state[buf] then return end
  state[buf] = { keys = true, hints = false, rainbow = true }
  define_highlights()
  vim.bo[buf].textwidth = 0
  vim.bo[buf].fileencoding = "utf-8"
  vim.bo[buf].bomb = false
  vim.bo[buf].fileformat = "unix"
  vim.api.nvim_set_option_value("colorcolumn", tostring(M.line_max + 1), { win = vim.api.nvim_get_current_win() })
  set_keys(buf, true)
  map_mouse(buf)
  vim.keymap.set("n", "K", M.hover, { buffer = buf, desc = "emd: instruction under the cursor" })
  local group = vim.api.nvim_create_augroup("emd." .. buf, {})
  vim.api.nvim_create_autocmd({ "TextChanged", "TextChangedI" }, {
    group = group, buffer = buf, callback = function() changed(buf) end,
  })
  vim.api.nvim_create_autocmd("BufWipeout", {
    group = group, buffer = buf, callback = function() state[buf] = nil end,
  })
  changed(buf)
end

return M
