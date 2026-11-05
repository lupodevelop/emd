<picture>
  <source media="(prefers-color-scheme: dark)" srcset="assets/logo-on-dark.svg">
  <img src="assets/logo-on-light.svg" alt="emd" width="320">
</picture>

**emd** — short for *em dash*. Also **Emotional damage**.

A programming language written entirely in dashes.

```
-‐-‑‑-–‒
```

That's a program. It adds 1 and 2. Those are five different characters, `U+002D U+2010 U+002D U+2011 U+2011 U+002D U+2013 U+2012`, and your font is not going to help you.

AI loves em dashes. We made them executable.

**[Try it in your browser](https://lupodevelop.github.io/emd/keyboard/)** · [Website](https://lupodevelop.github.io/emd/) · [Paper](https://lupodevelop.github.io/emd/paper/)

## Run it

Check [Releases](https://github.com/lupodevelop/emd/releases) for prebuilt CLI packages with examples and documentation. To build from a checkout, you need [Rust](https://rustup.rs):

```
cargo install --path crates/emd-cli
emd run examples/hello.emd
```

## How it works

Eight dashes. Two make an instruction. Thirty-two instructions, one stack. No keywords, no spaces, no comments, no second chances: type U+2013 where you meant U+2014 and you wrote a different program, or none at all.

Lines stop at 32 dashes. You can break them anywhere, even inside an instruction, and every newline is thrown away before decoding, so the shape of the program means nothing at all.

Nobody should write this by hand, so there's an assembler:

```
; prints the digits 3 2 1
CONST COUNTER 0

  PUSH 3 STORE COUNTER
loop:
  LOAD COUNTER PUSH '0' ADD WRITE
  LOAD COUNTER PUSH 1 SUB DUP STORE COUNTER
  JNZ loop
  HALT
```

`emd asm countdown.asm > countdown.emd`. There's also Hello World, FizzBuzz and a [Brainfuck interpreter](examples/brainfuck.asm) in [`examples/`](examples). The `.asm` is what a human reads. The `.emd` is the program.

## Is this serious?

The syntax is a joke. The rest isn't.

- **It's Turing complete**, proved twice, in Lean and in Rocq, by simulating Turing machines directly. Eleven of the instructions are enough.
- **The compiler and the static analyzer are proved correct**, on models of them. So is the 64-bit machine.
- **The Rust is not proved.** No proof reaches it. Bounded model checking on every instruction and tens of thousands of comparisons against the models get close.

Lean theorems and Rocq theorems, with no `sorry`, no `Admitted` and no declared axiom. [What's proved, what's only tested, and what nobody has checked](docs/verification.md). `scripts/verify.sh` reruns it.

## The AI part

*We* asked Claude models for emd programs, "source only", and scored the exact bytes with the real compiler. A third of Haiku's right answers came back in Markdown and got thrown out. One sentence in the prompt fixed that, and made usable answers cheaper. [What we measured, what it cost and how to read it](benchmarks/llm/README.md).

## The tools

Far too good for what they're used for.

```
emd debug hello.emd      # a debugger that also runs backward
emd analyze hello.emd    # which faults are ruled out, for every input
emd c hello.emd          # compile to C, then to native code
emd doctor broken.emd    # why it won't decode, by name of the dash you got wrong
emd slop essay.txt       # run the dashes hiding in any text
```

`emd --help` lists the rest. There's also a [Neovim studio](editors/nvim) with a clickable keyboard and a meter of emotional damage.

Exit codes: 0 success, 1 decoding error or fault, 2 wrong usage, 3 no verdict from `verify` or `analyze`.

## The manual

[Instructions](docs/isa.md) · [Semantics](docs/semantics.md) · [Source format](docs/language-spec.md) · [Assembly](docs/assembly.md) · [Tools](docs/tools.md) · [Your first program](docs/studio.md)

[Changelog](CHANGELOG.md).

## What's where

| Path | |
| --- | --- |
| `crates/` | The language in Rust: `emd-core`, `emd-parser`, `emd-vm`, `emd-asm`, `emd-c`, `emd-analyze`, `emd-tools`, `emd-cli`, `emd-wasm` |
| `formal/` | The Lean and Rocq models and proofs |
| `editors/nvim` | The Neovim plugin |
| `benchmarks/llm` | The experiment on language models |
| `paper/emd.pdf` | The paper |
| `website/` | The site |

Everything above `emd-core` depends only on the layers below it, and the parser, both compilers and the analyzer do no I/O.

*If you're asking "Why?", you're probably asking the wrong question. The answer is obviously "Why not?"*

## License

MIT.
