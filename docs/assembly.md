# emd assembly

`emd asm` compiles a readable language to dashes. It's a separate tool: `.emd` files never contain any of it.

```
; prints the digits 3 2 1
CONST COUNTER 0         ; a name for a value

  PUSH 3
  STORE COUNTER
loop:                   ; a name for an address
  LOAD COUNTER
  PUSH '0' ADD WRITE
  LOAD COUNTER PUSH 1 SUB DUP STORE COUNTER
  JNZ loop
  HALT
```

## What it adds to the machine

| You write          | It compiles to                                                       |
| ------------------ | -------------------------------------------------------------------- |
| `PUSH 104`         | Instructions building 104: the machine only has literals 0 to 7      |
| `PUSH -3`          | `PUSH 0`, `PUSH 3`, `SUB`                                            |
| `PUSH 'h'`         | The code point as an integer. Escapes: `\n \t \r \0 \\ \" \'`        |
| `PUSH NAME`        | The value of a `CONST`                                               |
| `LOAD x`           | `PUSH x`, `LOAD`                                                     |
| `STORE x`          | `PUSH x`, `STORE`                                                    |
| `JMP l`, `JZ l`, `JNZ l`, `CALL l` | Instructions building the offset to label `l`, then the jump |
| `PRINT "text"`     | `PUSH byte`, `WRITE` for each UTF-8 byte                             |
| `CONST NAME value` | Nothing: defines a name, usable after this line                      |
| `name:`            | Nothing: names the next instruction                                  |

Every instruction in [isa.md](isa.md) is also valid as written, including jumps with no operand, which take their offset from the stack.

## Rules

- Whitespace separates tokens, and an instruction and its operand share a line. `;` starts a comment.
- Instruction names ignore case. Your own names don't.
- A name can't be an instruction name: `JNZ halt` would have two readings.
- Integers must fit in `-(2^63 - 1) ..= 2^63 - 1`.
- Diagnostics include the token position.

```
error: undefined label `nope`
 --> broken.asm:2:7
  |
2 |   JNZ nope
  |       ^^^^
```

## How jumps get their length

An offset is built from instructions, so its length depends on its value. Its value depends on the lengths of the jumps it crosses. The compiler gives each jump a slot that only grows, and repeats until nothing changes. A slot longer than needed gets filled with no-ops (`PUSH 0`, `ADD`).

Lean proves this on a copy of the code generator, and a test compares the two byte for byte: see [verification.md](verification.md).

`emd disasm` goes the other way. It prints flat instructions, which `emd asm` compiles back to the same bytes.

## The compiler in emd

`compiler/asm.asm` is this compiler written in emd assembly, and `compiler/asm.emd` is that file compiled. It compiles itself back to the same bytes:

```
emd run compiler/asm.emd < program.asm > program.emd
```

Its output is the same as `emd asm` on every program. On an error it prints only the line, then stops with a fault. A test compares the two on the examples, on itself and on thousands of random texts, valid or not.
