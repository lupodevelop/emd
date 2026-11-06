# emd for Neovim

Needs Neovim 0.10 or later and `emd` on the `PATH`, or in `EMD_BIN`.

## Install

With lazy.nvim, from a checkout:

```lua
{ dir = "/path/to/emd/editors/nvim" }
```

Or `set rtp^=/path/to/emd/editors/nvim`.

## The Studio

From the repository root, with your usual configuration:

```sh
editors/nvim/studio.sh examples/add.emd
```

`--clean` starts it without your configuration. If the plugin is installed, open a `.emd` file and run `:EmdStudio`. It opens a tab of debugger panels, and closing the tab takes you back.

[Write a program in Neovim Studio](../../docs/studio.md) walks through a first program. All commands and keys are in [docs/tools.md](../../docs/tools.md).

## While the Studio is open

- **Stepping.** In normal mode, Enter steps forward and Backspace steps back. `:EmdStep`, `:EmdBack`, `:EmdContinue` and `:EmdReset` do the same from the command line.
- **Editing.** The source accepts only the eight dashes and newlines. A paste with anything else is rejected whole, and invalid text already in the file stays there for the diagnostics to report.
- **Saving.** It runs a temporary copy of the buffer, so the next debugger action picks up your edit without saving, and debugging never writes to your file.
