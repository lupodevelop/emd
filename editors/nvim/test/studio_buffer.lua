-- Targeted regression: Studio must execute unsaved source without writing it.
-- EMD_BIN=... nvim --headless -n -u NONE -i NONE --cmd 'set rtp^=editors/nvim' \
--   -c 'luafile editors/nvim/test/studio_buffer.lua'
local path = vim.fn.tempname() .. '.emd'
local studio
local function test()
  vim.cmd('filetype plugin on')
  vim.cmd('runtime ftdetect/emd.lua')
  vim.cmd('runtime plugin/emd.lua')
  local emd = require('emd')
  local function keys(text)
    local result = vim.system({ emd.cli, 'keys' }, { stdin = text, text = true }):wait()
    assert(result.code == 0, result.stderr)
    return vim.trim(result.stdout)
  end
  local sum, echo = keys('asaddagf'), keys('hahsgf')
  vim.fn.writefile({ sum }, path)
  vim.cmd.edit(path)
  studio = require('emd.studio')
  studio.open()
  local function at(step, stack, output)
    assert(vim.wait(2000, function() return studio.state and studio.state.step == step end), 'missing step ' .. step)
    assert(vim.deep_equal(studio.state.stack, stack), vim.inspect(studio.state))
    assert(vim.deep_equal(studio.state.output, output or {}), vim.inspect(studio.state))
  end
  at(0, {})
  studio.send('c'); at(4, { 3 })
  studio.set_input('A'); at(0, {})
  -- No :write and no input reset after the edit: stepping itself must reload.
  vim.api.nvim_buf_set_lines(studio.source_buf, 0, -1, false, { echo })
  studio.send('s'); at(1, { 65 })
  assert(studio.listing[1] == 'READ' and studio.listing[2] == 'WRITE')
  studio.send('s'); at(2, {}, { 65 })
  studio.send('b'); at(1, { 65 })
  assert(vim.fn.readfile(path)[1] == sum, 'debugger overwrote the saved source')
  assert(vim.bo[studio.source_buf].modified, 'unsaved state was lost')
  local snapshot, input = studio.snapshot_file, studio.input_file
  studio.close()
  assert(vim.fn.filereadable(snapshot) == 0 and vim.fn.filereadable(input) == 0, 'temporary files not cleaned')
  print('PASS: unsaved buffer reload, current listing, step/back/output, original file preserved, temporary files cleaned')
end
local ok, err = xpcall(test, debug.traceback)
if studio then pcall(studio.close) end
vim.fn.delete(path)
if not ok then io.stderr:write(err .. '\n'); vim.cmd('cquit 1') end
vim.cmd('qa!')
