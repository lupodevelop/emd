# Write a program in Neovim Studio

Start here to type a program yourself. You need [the plugin](https://github.com/lupodevelop/emd/tree/main/editors/nvim) installed and `emd` built.

## Add 1 and 2

From the repository root, open a scratch file:

```sh
EMD_BIN="$PWD/target/debug/emd" nvim /tmp/emd-demo.emd
```

If the file has an old exercise in it, press Esc and type `ggdG` to clear it. Press `i` and type these letters, with no spaces:

**`asaddagf`**

Type them by hand instead of pasting: each letter turns into a dash as you go.

| Letters | Instruction | Effect |
| --- | --- | --- |
| `as` | PUSH 1 | Put 1 on the stack. |
| `ad` | PUSH 2 | Put 2 on top. |
| `da` | ADD | Replace both with their sum. |
| `gf` | HALT | Stop. |

Press Esc, run `:EmdStudio`, click the source window, press Esc and press Enter four times. You'll see the stack change:

```text
[] -> [1] -> [1, 2] -> [3] -> [3], halted
```

**The answer is the 3 on the stack.** The output stays empty, because the program has no `WRITE`. Backspace steps back, and `:EmdReset` starts over.

## Print A

In the source window, press Esc, type `ggdG`, press `i` and type:

**`asakddaddaakddaddahsgf`**

Press Esc and run `:EmdContinue`. **A appears in the output panel.**

The machine has no literal above 7, so the program builds 65 and writes it. The pairs are `as ak dd ad da ak dd ad da hs gf`:

```text
PUSH 1, PUSH 7, MUL, PUSH 2, ADD, PUSH 7, MUL, PUSH 2, ADD, WRITE, HALT
```

## Good to know

| Mode | Enter | Backspace |
| --- | --- | --- |
| Insert, after `i` | New line | Delete |
| Normal, after Esc, in the source window | Run one instruction | Step back |

- Click the source window before typing or stepping.
- **You don't need to save to test an edit.** The next debugger action picks it up and restarts the program. `:w` saves when you want to.
- The source takes only dashes and newlines, so pasting ordinary letters is rejected.
- `:EmdHints` shows instruction names. In the panels, `top` marks the top of the stack.
- A program with `READ` needs input: `:EmdInput A`. With no input, `READ` gives -1, and passing that to `WRITE` faults with `-1 is not a byte`.
- Close the Studio with `:tabclose` before opening it on another file.
