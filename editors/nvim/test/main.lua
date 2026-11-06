-- Entry point: an error in the tests must end Neovim, not leave it waiting.
local ok, err = xpcall(dofile, debug.traceback, "editors/nvim/test/run.lua")
if not ok then
  io.stderr:write(tostring(err) .. "\n")
  vim.cmd("cquit 1")
end
