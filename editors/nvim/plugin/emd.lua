local function emd() return require("emd") end
local command = vim.api.nvim_create_user_command

command("EmdKeyboard", function() emd().toggle_keyboard() end, { desc = "Clickable keyboard of dashes and instructions" })
command("EmdFmt", function() emd().format() end, { desc = "Rewrap the buffer in lines of 32" })
command("EmdKeys", function() emd().toggle_keys() end, { desc = "Letters asdfghjk type dashes in insert mode" })
command("EmdHints", function() emd().toggle_hints() end, { desc = "Show the mnemonic after each instruction" })
command("EmdRainbow", function() emd().toggle_rainbow() end, { desc = "One color every 16 code points, meaning nothing" })
command("EmdRun", function() emd().terminal("run") end, { desc = "emd run in a terminal" })
command("EmdDebug", function() emd().terminal("debug") end, { desc = "emd debug in a terminal" })
for _, tool in ipairs({ "inspect", "explain", "disasm", "doctor", "verify", "check", "analyze", "cfg", "c", "profile", "reduce", "slop" }) do
  local name = "Emd" .. tool:sub(1, 1):upper() .. tool:sub(2)
  command(name, function() emd().report(tool) end, { desc = "emd " .. tool })
end
command("EmdStudio", function() require("emd.studio").open() end, { desc = "Source, debugger panels, keyboard, and regret" })
for name, entry in pairs({
  EmdStep = { "s", "Step forward" },
  EmdBack = { "b", "Step backward" },
  EmdContinue = { "c", "Continue execution" },
  EmdReset = { "goto 0", "Restart execution" },
}) do
  command(name, function()
    local studio = require("emd.studio")
    if not studio.source_buf or not vim.api.nvim_buf_is_valid(studio.source_buf) then
      vim.notify("emd: open :EmdStudio first", vim.log.levels.WARN)
      return
    end
    studio.send(entry[1])
  end, { desc = entry[2] .. " in the emd Studio" })
end
command("EmdInput", function(o) require("emd.studio").set_input(o.args) end, { nargs = "?", desc = "Input for the studio debugger" })
