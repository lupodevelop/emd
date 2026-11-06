-- The studio: the source in the middle, a live debugger around it through
-- `emd debug --machine`, the keyboard, and a meter nobody asked for.
local emd = require("emd")
local S = { win = {}, buf = {}, input = "" }
local ns = vim.api.nvim_create_namespace("emd.studio")

local KEYS = {
  { "<F5>", "c", "continue" }, { "<F6>", "rc", "continue backward" },
  { "<F8>", "b", "step back" }, { "<F10>", "s", "step" },
}

-- What each dash is like, as the website says it.
local VERDICTS = {
  "The one on your keyboard.", "Already a different character.", "Refuses to break. Will break you.",
  "A figure of your imagination.", "Half an em. Twice the doubt.", "The reason we are all here.",
  "The bar was already low.", "Subtracts from your sanity.",
}
local FAULT_LINES = {
  "Emotional damage.", "It did exactly what you wrote.", "The dash you meant was a different dash.",
  "The proofs still hold. You do not.", "Nothing here is undefined. This is your fault, formally.",
}

local function scratch(name)
  local buf = vim.api.nvim_create_buf(false, true)
  vim.bo[buf].bufhidden = "hide"
  vim.bo[buf].filetype = "emdpanel"
  pcall(vim.api.nvim_buf_set_name, buf, "emd://" .. name)
  return buf
end

local function fill(buf, lines)
  vim.api.nvim_buf_set_lines(buf, 0, -1, false, lines)
end

local function panel(name, title, config)
  local buf = scratch(name)
  local win = vim.api.nvim_open_win(buf, false, config)
  vim.wo[win].number = false
  vim.wo[win].relativenumber = false
  vim.wo[win].signcolumn = "no"
  vim.wo[win].list = false
  vim.wo[win].wrap = false
  vim.wo[win].winbar = " " .. title
  S.buf[name], S.win[name] = buf, win
end

local function highlights()
  vim.api.nvim_set_hl(0, "EmdPc", { reverse = true, bold = true, default = true })
  vim.api.nvim_set_hl(0, "EmdBreak", { fg = "#e06c75", ctermfg = 1, bold = true, default = true })
  vim.api.nvim_set_hl(0, "EmdFault", { fg = "#e06c75", ctermfg = 1, bold = true, default = true })
  vim.api.nvim_set_hl(0, "EmdOk", { fg = "#98c379", ctermfg = 2, bold = true, default = true })
end

local function text_of(bytes)
  local parts = {}
  for _, b in ipairs(bytes) do
    if b == 10 or (b >= 32 and b < 127) then parts[#parts + 1] = string.char(b)
    else parts[#parts + 1] = string.format("\\x%02X", b) end
  end
  return vim.split(table.concat(parts), "\n")
end

local function int(v) return string.format("%.0f", v) end

local function damage_lines()
  local points = emd.code_points(S.source_buf)
  local counts = {}
  for i = 1, 8 do counts[i] = 0 end
  local index = {}
  for i, code in ipairs(emd.codes) do index[vim.fn.nr2char(code)] = i end
  for _, p in ipairs(points) do
    local i = index[p.char]
    if i then counts[i] = counts[i] + 1 end
  end
  local widest = math.max(1, unpack(counts))
  local lines = {}
  for i = 1, 8 do
    local bar = string.rep(vim.fn.nr2char(emd.codes[i]), math.ceil(18 * counts[i] / widest))
    lines[#lines + 1] = string.format("%04X %5d %s", emd.codes[i], counts[i], bar)
  end
  local total = math.max(1, #emd.dashes(points))
  S.faults = S.faults or 0
  S.rewinds = S.rewinds or 0
  lines[#lines + 1] = ""
  lines[#lines + 1] = string.format("em dash density  %5.1f%%", 100 * counts[6] / total)
  lines[#lines + 1] = "readable by you    0.0%"
  lines[#lines + 1] = string.format("faults survived  %6d", S.faults)
  lines[#lines + 1] = string.format("times regretted  %6d", S.rewinds)
  lines[#lines + 1] = string.format("sanity           %5d%%", math.max(0, 100 - 7 * S.faults - S.rewinds))
  local row, col = unpack(vim.api.nvim_win_get_cursor(S.source_win))
  for _, p in ipairs(points) do
    if p.line == row - 1 and col >= p.from and col < p.to and index[p.char] then
      lines[#lines + 1] = ""
      lines[#lines + 1] = VERDICTS[index[p.char]]
    end
  end
  return lines
end

local function paint_damage()
  if not (S.source_win and vim.api.nvim_win_is_valid(S.source_win)) then return end
  if S.buf.damage and vim.api.nvim_buf_is_valid(S.buf.damage) then fill(S.buf.damage, damage_lines()) end
end

local function render(state)
  S.state = state
  local valid = vim.api.nvim_win_is_valid
  if not (S.source_win and valid(S.source_win)) then return end
  local faulted = state.status:sub(1, 5) == "fault"
  if faulted and S.last_status ~= state.status then
    S.faults = (S.faults or 0) + 1
    S.fault_line = FAULT_LINES[S.faults % #FAULT_LINES + 1]
  end
  S.last_status = state.status

  -- Source: the pair about to run.
  vim.api.nvim_buf_clear_namespace(S.source_buf, ns, 0, -1)
  local dashes = emd.dashes(emd.code_points(S.source_buf))
  local first, second = dashes[state.pc * 2 + 1], dashes[state.pc * 2 + 2]
  if first and second then
    -- The two halves of a pair may sit on different lines.
    for _, half in ipairs({ first, second }) do
      vim.api.nvim_buf_set_extmark(S.source_buf, ns, half.line, half.from, { end_col = half.to, hl_group = "EmdPc", priority = 300 })
    end
    vim.api.nvim_win_set_cursor(S.source_win, { first.line + 1, first.from })
  end
  local name = S.listing and S.listing[state.pc + 1] or "-"
  vim.wo[S.source_win].winbar = string.format(" step %d  pc %d  %s  %s", state.step, state.pc, name, faulted and (state.status .. " | " .. S.fault_line) or state.status)

  -- Listing: pc and breakpoints.
  local lb = S.buf.listing
  vim.api.nvim_buf_clear_namespace(lb, ns, 0, -1)
  local is_break = {}
  for _, b in ipairs(state.breaks) do is_break[b] = true end
  for b in pairs(is_break) do
    if b < vim.api.nvim_buf_line_count(lb) then
      vim.api.nvim_buf_set_extmark(lb, ns, b, 0, { virt_text = { { "*", "EmdBreak" } }, virt_text_pos = "right_align" })
    end
  end
  if state.pc < vim.api.nvim_buf_line_count(lb) then
    vim.api.nvim_buf_set_extmark(lb, ns, state.pc, 0, { line_hl_group = faulted and "EmdFault" or "EmdPc" })
    if valid(S.win.listing) then vim.api.nvim_win_set_cursor(S.win.listing, { state.pc + 1, 0 }) end
  end

  local stack = {}
  for i = #state.stack, math.max(1, #state.stack - 200), -1 do
    stack[#stack + 1] = string.format("%-4s%s", i == #state.stack and "top" or "", int(state.stack[i]))
  end
  fill(S.buf.stack, #stack > 0 and stack or { "(empty)" })
  local memory = {}
  for _, cell in ipairs(state.memory) do memory[#memory + 1] = string.format("[%s] = %s", int(cell[1]), int(cell[2])) end
  fill(S.buf.memory, #memory > 0 and memory or { "(all zero)" })
  fill(S.buf.output, text_of(state.output))
  paint_damage()
  if S.waiting then
    local done = S.waiting
    S.waiting = nil
    done(state)
  end
end

local refresh_static

local function source_text()
  return table.concat(vim.api.nvim_buf_get_lines(S.source_buf, 0, -1, false), "\n") .. "\n"
end

-- The editor buffer is the program being debugged. Keep its snapshot separate
-- from the user's file: stepping must neither run stale disk contents nor save.
local function source_file()
  S.snapshot_file = S.snapshot_file or (vim.fn.tempname() .. ".emd")
  local text = source_text()
  local handle = assert(io.open(S.snapshot_file, "wb"))
  handle:write(text)
  handle:close()
  return S.snapshot_file, text
end

local function stop_debugger()
  S.debug_generation = (S.debug_generation or 0) + 1
  if S.job then
    pcall(function() S.job:write("q\n") end)
    pcall(function() S.job:kill(9) end)
    S.job = nil
  end
  if S.input_file then os.remove(S.input_file); S.input_file = nil end
end

local function start_debugger()
  stop_debugger()
  local file, text = source_file()
  S.loaded_text, S.state, S.last_status = text, nil, nil
  local generation = S.debug_generation
  fill(S.buf.stack, { "(starting current source)" })
  fill(S.buf.memory, { "(all zero)" })
  fill(S.buf.output, { "" })
  local args = { emd.cli, "debug", file }
  local stdin = vim.fn.tempname()
  S.input_file = stdin
  local handle = assert(io.open(stdin, "wb"))
  handle:write(S.input)
  handle:close()
  vim.list_extend(args, { "--input", stdin, "--machine" })
  local pending = ""
  S.job = vim.system(args, {
    stdin = true,
    stdout = function(_, data)
      if not data then return end
      pending = pending .. data
      while true do
        local line, rest = pending:match("^(.-)\n(.*)$")
        if not line then break end
        pending = rest
        local ok, state = pcall(vim.json.decode, line)
        if ok then vim.schedule(function()
          if S.debug_generation == generation then render(state) end
        end) end
      end
    end,
    stderr = function(_, data)
      if data and data ~= "" then
        vim.schedule(function()
          if S.debug_generation == generation and S.source_win and vim.api.nvim_win_is_valid(S.source_win) then
            vim.wo[S.source_win].winbar = " " .. data:gsub("\n", " ")
          end
        end)
      end
    end,
  })
end

function S.send(command)
  if not S.job or S.loaded_text ~= source_text() then
    refresh_static()
    start_debugger()
  end
  if command:sub(1, 1) == "b" or command == "rc" then S.rewinds = (S.rewinds or 0) + 1 end
  pcall(function() S.job:write(command .. "\n") end)
end

-- A breakpoint at the instruction under the cursor in the source.
function S.toggle_break()
  local row, col = unpack(vim.api.nvim_win_get_cursor(S.source_win))
  for i, p in ipairs(emd.dashes(emd.code_points(S.source_buf))) do
    if p.line == row - 1 and col >= p.from and col < p.to then
      local pc = math.floor((i - 1) / 2)
      local set = false
      for _, b in ipairs(S.state and S.state.breaks or {}) do set = set or b == pc end
      S.send((set and "del " or "break ") .. pc)
      return
    end
  end
end

-- Steps on a timer with the colors cycling, until it ends or F4 comes again.
function S.toggle_play()
  if S.timer then
    S.timer:stop()
    S.timer = nil
    emd.set_rainbow_offset(S.source_buf, 0)
    return
  end
  local tick = 0
  S.timer = vim.uv.new_timer()
  S.timer:start(0, 90, vim.schedule_wrap(function()
    if not S.timer then return end
    if S.state and S.state.status ~= "running" then
      S.toggle_play()
      return
    end
    tick = tick + 1
    emd.set_rainbow_offset(S.source_buf, tick)
    S.send("s")
  end))
end

function S.set_input(text)
  S.input = (text or ""):gsub("\\n", "\n")
  if S.source_buf then refresh_static(); start_debugger() end
end

refresh_static = function()
  local file = source_file()
  local disasm = vim.system({ emd.cli, "disasm", file }, { text = true }):wait()
  local names = vim.split(disasm.stdout or "", "\n", { trimempty = true })
  S.listing = names
  local lines = {}
  for i, name in ipairs(names) do lines[i] = string.format("%5d  %s", i - 1, name) end
  if disasm.code ~= 0 then lines = vim.split(disasm.stderr or "does not decode", "\n", { trimempty = true }) end
  fill(S.buf.listing, lines)
  local analysis = vim.system({ emd.cli, "analyze", file }, { text = true }):wait()
  local report = vim.split(analysis.stdout ~= "" and analysis.stdout or (analysis.stderr or ""), "\n", { trimempty = true })
  fill(S.buf.analysis, report)
  vim.api.nvim_buf_clear_namespace(S.buf.analysis, ns, 0, -1)
  for i, line in ipairs(report) do
    local hl = line:find("^proved") and "EmdOk" or line:find("^not proved") and "EmdFault"
    if hl then vim.api.nvim_buf_set_extmark(S.buf.analysis, ns, i - 1, 0, { end_col = #line, hl_group = hl }) end
  end
end

function S.open()
  if S.source_win and vim.api.nvim_win_is_valid(S.source_win) then
    vim.api.nvim_set_current_win(S.source_win)
    return
  end
  local name = vim.api.nvim_buf_get_name(0)
  if name == "" or vim.bo.filetype ~= "emd" then
    vim.notify("emd: open a .emd file first, such as :edit program.emd", vim.log.levels.WARN)
    return
  end
  highlights()
  vim.cmd("tab split")
  S.source_win, S.source_buf = vim.api.nvim_get_current_win(), vim.api.nvim_get_current_buf()
  vim.wo[S.source_win].wrap = true
  vim.wo[S.source_win].number = false
  vim.wo[S.source_win].relativenumber = false
  vim.wo[S.source_win].signcolumn = "no"
  -- The source comes first: on a narrow terminal the panels give way.
  panel("listing", "listing", { split = "left", win = S.source_win, width = math.min(40, math.floor(vim.o.columns * 0.25)) })
  panel("analysis", "analysis", { split = "below", win = S.win.listing, height = math.floor(vim.o.lines * 0.36) })
  vim.wo[S.win.analysis].wrap = true
  vim.wo[S.win.analysis].linebreak = true
  panel("stack", "stack", { split = "right", win = S.source_win, width = math.min(34, math.floor(vim.o.columns * 0.22)) })
  panel("memory", "memory", { split = "below", win = S.win.stack, height = 7 })
  panel("output", "output", { split = "below", win = S.win.memory, height = 7 })
  panel("damage", "emotional damage", { split = "below", win = S.win.output, height = 17 })
  local keyboard = emd.open_keyboard(S.source_win)
  if keyboard then
    vim.wo[keyboard].number = false
    vim.wo[keyboard].relativenumber = false
    vim.wo[keyboard].signcolumn = "no"
    vim.wo[keyboard].list = false
    vim.wo[keyboard].winbar = " keyboard: click, or type a s d f g h j k"
  end
  S.win.keyboard = keyboard
  local buf = S.source_buf
  local function map(key, fn, desc) vim.keymap.set({ "n", "i" }, key, fn, { buffer = buf, desc = "emd: " .. desc }) end
  for _, entry in ipairs(KEYS) do map(entry[1], function() S.send(entry[2]) end, entry[3]) end
  map("<F4>", S.toggle_play, "play")
  map("<F7>", function() S.send("goto 0") end, "back to the start")
  map("<F9>", S.toggle_break, "breakpoint")
  -- Terminal-friendly controls, in normal mode only. Preserve local user maps.
  S.normal_maps = {}
  for _, entry in ipairs({ { "<CR>", "s", "step" }, { "<BS>", "b", "step back" } }) do
    local previous = vim.fn.maparg(entry[1], "n", false, true)
    S.normal_maps[entry[1]] = previous.buffer == 1 and previous or false
    vim.keymap.set("n", entry[1], function() S.send(entry[2]) end,
      { buffer = buf, desc = "emd: " .. entry[3] })
  end
  local group = vim.api.nvim_create_augroup("emd.studio", {})
  local allowed = {}
  for _, code in ipairs(emd.codes) do allowed[code] = true end
  local accepted = vim.api.nvim_buf_get_lines(buf, 0, -1, false)
  local accepted_cursor = vim.api.nvim_win_get_cursor(S.source_win)
  local function allowed_text(lines)
    for _, line in ipairs(lines) do
      for _, code in ipairs(vim.fn.str2list(line, true)) do
        if not allowed[code] then return false end
      end
    end
    return true
  end
  vim.api.nvim_create_autocmd("InsertCharPre", {
    group = group, buffer = buf,
    callback = function()
      if not allowed_text({ vim.v.char }) then vim.v.char = "" end
    end,
  })
  -- Paste and normal-mode edits bypass InsertCharPre. Reject the whole change,
  -- keeping the previous source rather than silently deleting parts of a paste.
  vim.api.nvim_create_autocmd({ "TextChanged", "TextChangedI", "TextChangedP", "BufWritePre" }, {
    group = group, buffer = buf,
    callback = function()
      local lines = vim.api.nvim_buf_get_lines(buf, 0, -1, false)
      if allowed_text(lines) then
        accepted = lines
        if vim.api.nvim_win_is_valid(S.source_win) then
          accepted_cursor = vim.api.nvim_win_get_cursor(S.source_win)
        end
      elseif not vim.deep_equal(lines, accepted) then
        vim.api.nvim_buf_call(buf, function()
          pcall(vim.cmd, "undojoin")
          vim.api.nvim_buf_set_lines(buf, 0, -1, false, accepted)
        end)
        if vim.api.nvim_win_is_valid(S.source_win) then
          vim.api.nvim_win_set_cursor(S.source_win, accepted_cursor)
        end
        vim.notify("emd: edit rejected; only the eight dashes and newlines are allowed", vim.log.levels.WARN)
      end
    end,
  })
  vim.api.nvim_create_autocmd("BufWritePost", {
    group = group, buffer = buf,
    callback = function()
      refresh_static()
      start_debugger()
    end,
  })
  vim.api.nvim_create_autocmd("CursorMoved", { group = group, buffer = buf, callback = paint_damage })
  vim.api.nvim_create_autocmd({ "TextChanged", "TextChangedI" }, {
    group = group, buffer = buf, callback = function()
      paint_damage()
      if S.loaded_text ~= source_text() and S.source_win and vim.api.nvim_win_is_valid(S.source_win) then
        vim.wo[S.source_win].winbar = " source changed | Esc, Enter: restart with current source"
      end
    end,
  })
  vim.api.nvim_create_autocmd("VimLeavePre", { group = group, callback = stop_debugger })
  -- Closing the source window ends the studio, however it gets closed.
  vim.api.nvim_create_autocmd("WinClosed", {
    group = group, pattern = tostring(S.source_win), callback = vim.schedule_wrap(function() S.close() end),
  })
  refresh_static()
  start_debugger()
  vim.api.nvim_set_current_win(S.source_win)
end

function S.close()
  stop_debugger()
  if S.snapshot_file then os.remove(S.snapshot_file); S.snapshot_file = nil end
  S.loaded_text = nil
  if S.timer then S.toggle_play() end
  pcall(vim.api.nvim_del_augroup_by_name, "emd.studio")
  if S.source_buf and vim.api.nvim_buf_is_valid(S.source_buf) then
    vim.api.nvim_buf_call(S.source_buf, function()
      for key, previous in pairs(S.normal_maps or {}) do
        pcall(vim.keymap.del, "n", key, { buffer = S.source_buf })
        if previous then vim.fn.mapset("n", false, previous) end
      end
    end)
    S.normal_maps = nil
    for _, key in ipairs({ "<F4>", "<F5>", "<F6>", "<F7>", "<F8>", "<F9>", "<F10>" }) do
      pcall(vim.keymap.del, { "n", "i" }, key, { buffer = S.source_buf })
    end
    vim.api.nvim_buf_clear_namespace(S.source_buf, ns, 0, -1)
  end
  for _, buf in pairs(S.buf) do
    if vim.api.nvim_buf_is_valid(buf) then vim.api.nvim_buf_delete(buf, { force = true }) end
  end
  S.win, S.buf, S.source_win, S.source_buf, S.state, S.last_status = {}, {}, nil, nil, nil, nil
end

return S
