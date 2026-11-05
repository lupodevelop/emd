<picture>
  <source media="(prefers-color-scheme: dark)" srcset="assets/logo-on-dark.svg">
  <img src="assets/logo-on-light.svg" alt="emd" width="320">
</picture>

**emd** — short for *em dash*. Also **Emotional damage**.

A programming language written entirely in dashes.

AI loves em dashes. We made them executable.

```
-‐-‑‑-–‒
```

This adds 1 and 2. Those are five different characters. Your font may disagree.

Eight Unicode dashes form the alphabet. Each pair is an instruction, and there
are 32 instructions in all. No spaces, keywords or comments. Lines stop at 32
dashes; line breaks otherwise have no meaning.

You can [try it in your browser](https://lupodevelop.github.io/emd/keyboard/).

## Run it

With Rust installed, from a checkout:

```sh
cargo install --path crates/emd-cli
emd run examples/hello.emd
```

There is a readable assembler for when the joke wears off:

```asm
PRINT "Hello, world!\n"
HALT
```

Save that as `hello.asm`, then:

```sh
emd asm hello.asm > hello.emd
emd run hello.emd
```

The examples go from adding two numbers to FizzBuzz and a Brainfuck interpreter.
The [manual](https://lupodevelop.github.io/emd/docs/) covers the instructions,
assembly and tools.

## Under the dashes

A stack machine with memory, arithmetic, jumps and calls. A debugger lets you
step through it in either direction. There is also static analysis, a C backend
and a Neovim Studio for writing programs without memorizing Unicode code points.

The language is Turing complete, with proofs in Lean and Rocq. Correctness proofs
for the compiler and analyzer concern formal models; the Rust implementation is
checked with bounded verification and comparisons against those models.

The [paper](https://lupodevelop.github.io/emd/paper/) covers the semantics and
proofs, and an experiment on language models: how often correct code becomes
unusable because the answer arrives wrapped in Markdown.

*If you're asking "Why?", you're probably asking the wrong question. The answer is obviously "Why not?"*

## License

MIT.
