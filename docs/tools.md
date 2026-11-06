# Tools

`emd --help` lists everything. This page covers the ones that need more than a line. To write a program yourself, start with [the Studio walkthrough](studio.md).

## Typing dashes

Nobody can type eight kinds of dash, so eight letters stand in for them, in alphabet order:

| Letter | `a` | `s` | `d` | `f` | `g` | `h` | `j` | `k` |
| ------ | --- | --- | --- | --- | --- | --- | --- | --- |
| Index  | 0   | 1   | 2   | 3   | 4   | 5   | 6   | 7   |

An instruction is two letters: family, then operation. `ADD` is family 2, operation 0, so `da`. `HALT` is `gf`. So `asaddagf` adds 1 and 2.

The letters only help you type. `.emd` files hold dashes.

- `emd keys` turns letters into dashes, from a file or stdin. In any editor: `:%!emd keys`.
- The [website keyboard](https://lupodevelop.github.io/emd/keyboard/) takes letters or clicks, decodes as you type and runs the program.
- [`editors/nvim`](https://github.com/lupodevelop/emd/tree/main/editors/nvim) does the same in Neovim.

## Analysis

`emd analyze` looks at the whole program without running it, and its answers hold for every input. It reports what's reachable, what's dead code and which faults it can rule out: stack underflow, a `pc` outside the program, a jump to an unknown target, division by zero, a negative address and a non-byte `WRITE`. On every program in `examples/` it rules out all of them, including the Brainfuck interpreter running any Brainfuck program.

It tracks each value as a set of possible integers, or a range past 512 of them. It also remembers how values relate, so a test on one narrows the others. In `READ DUP PUSH 1 ADD JZ end`, the byte past the jump can't be -1.

When it can't tell, it says so. That happens with a jump to a value it can't list, deep recursion and very long loops. It doesn't analyze overflow on values it doesn't know exactly, resource limits or termination.

Exit code 0 means everything it checks is proved, and 3 means something isn't. `not proved` doesn't mean a bug. Only `certain if reached` says the instruction faults every time it runs.

## Other commands

- `emd cfg` prints the control flow graph for Graphviz.
- `emd c` compiles to C, with the same faults and limits as the VM except the step limit.
- `emd profile` counts steps per instruction.
- `emd reduce` shrinks a program while keeping its output and how it ends.
- `emd slop` keeps only the dashes of any text and runs them, skipping the pairs that mean nothing. AI loves em dashes, so try it on an essay. It usually ends in a fault.

## Debugger

```
emd debug program.emd --input input.txt
```

Input comes from a file, because stdin carries the debugger's commands. An empty line repeats the last command.

| Command     | Effect                                         |
| ----------- | ---------------------------------------------- |
| `s [n]`     | Step forward                                   |
| `b [n]`     | Step back                                      |
| `c`         | Continue to a breakpoint or the end            |
| `rc`        | Continue backward to the previous breakpoint   |
| `goto n`    | Move to step `n`, in either direction          |
| `break pc`  | Set a breakpoint; `del pc` removes it          |
| `p`         | State, nonzero memory and output               |
| `l`         | The instructions around `pc`                   |
| `mem a`     | The value of a cell                            |
| `why a`     | The step that last wrote a cell                |
| `q`         | Quit                                           |

To go back, it runs the program again from the start. The machine is deterministic, so it reaches the same states, and you can even step back out of a fault. `c` stops after 10000000 steps, so a loop gives you the prompt back.

## Neovim

`editors/nvim` is a plugin with no dependencies. It needs Neovim 0.10 or later and `emd` on the `PATH` or in `EMD_BIN`.

In a `.emd` buffer:

- The letters above type dashes in insert mode. `:EmdKeys` turns that off.
- `:EmdKeyboard` opens a clickable keyboard. It needs `set mouse=a`.
- Lines break by themselves at 32 dashes. `:EmdFmt` rewraps the whole buffer.
- `emd doctor` runs as you type and shows up as diagnostics.
- `K` names the instruction under the cursor. `:EmdHints` shows them all inline.
- `:EmdRainbow` toggles the colors: a new one every 16 dashes, meaning nothing.
- `:EmdRun` and `:EmdDebug` open a terminal. `:EmdInspect`, `:EmdExplain`, `:EmdDisasm`, `:EmdDoctor`, `:EmdVerify`, `:EmdCheck`, `:EmdAnalyze`, `:EmdCfg`, `:EmdC`, `:EmdProfile`, `:EmdReduce` and `:EmdSlop` open a report.

`:EmdStudio` opens everything at once: the source, the instruction listing, the analysis, stack, memory, output, the keyboard and a meter of emotional damage.

| Key   | Effect             |
| ----- | ------------------ |
| `F10` | Step               |
| `F8`  | Step back          |
| `F5`  | Continue           |
| `F6`  | Continue backward  |
| `F4`  | Play               |
| `F7`  | Restart            |
| `F9`  | Set a breakpoint   |

`:EmdInput text` sets the program's input. `editors/nvim/studio.sh file.emd` opens the Studio with your configuration, and `--clean` opens it without.
