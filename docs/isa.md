# Instruction Set Architecture

Every instruction is a pair of symbols. The first selects the family, the second the operation. Pairs not listed are **unassigned**: the decoder rejects them with an error, it does not skip them.

Operand convention: `b` is the value on top of the stack, `a` the one below. Binary instructions pop `b`, then `a`, and push the result.

## Alphabet

| Index | Symbol | Code point | Unicode name        |
| ------ | ------- | ---------- | ------------------- |
| 0      | `-`     | U+002D     | HYPHEN-MINUS        |
| 1      | `‐`     | U+2010     | HYPHEN              |
| 2      | `‑`     | U+2011     | NON-BREAKING HYPHEN |
| 3      | `‒`     | U+2012     | FIGURE DASH         |
| 4      | `–`     | U+2013     | EN DASH             |
| 5      | `—`     | U+2014     | EM DASH             |
| 6      | `―`     | U+2015     | HORIZONTAL BAR      |
| 7      | `−`     | U+2212     | MINUS SIGN          |

## Source layout

A source holds only these eight symbols and newlines (U+000A). A line holds at most 32 symbols; a longer line is an error. Every newline is removed before decoding, so a break can fall anywhere, even inside an instruction.

## Assigned instructions (32 of 64)

| Family       | Op | Code | Instruction | Effect                                                        |
| -------------- | -- | ------ | ---------- | -------------------------------------------------------------- |
| 0 `-` Constants | 0–7 | `-`·s | PUSH n     | Pushes `n`, the index of the second symbol                     |
| 1 `‐` Stack    | 0  | `‐-`   | DUP        | `a` → `a a`                                                    |
|                | 1  | `‐‐`   | DROP       | `a` → ∅                                                        |
|                | 2  | `‐‑`   | SWAP       | `a b` → `b a`                                                  |
|                | 3  | `‐‒`   | OVER       | `a b` → `a b a`                                                |
|                | 4  | `‐–`   | ROT        | `a b c` → `b c a`                                              |
| 2 `‑` Arithmetic | 0 | `‑-`  | ADD        | `a b` → `a + b`                                                |
|                | 1  | `‑‐`   | SUB        | `a b` → `a − b`                                                |
|                | 2  | `‑‑`   | MUL        | `a b` → `a · b`                                                |
|                | 3  | `‑‒`   | DIV        | `a b` → `a / b` truncated toward zero; fault if `b = 0`         |
|                | 4  | `‑–`   | MOD        | `a b` → remainder of `a / b`, with the sign of `a`; fault if `b = 0` |
| 3 `‒` Memory   | 0  | `‒-`   | LOAD       | `a` → `M[a]`; fault if `a < 0`                                |
|                | 1  | `‒‐`   | STORE      | `v a` → ∅, `M[a] := v`; fault if `a < 0`                      |
| 4 `–` Control  | 0  | `–-`   | JMP        | `off` → ∅, `pc := pc + off`                                    |
|                | 1  | `–‐`   | JZ         | `c off` → ∅, `pc := pc + off` if `c = 0`, else `pc + 1`  |
|                | 2  | `–‑`   | JNZ        | `c off` → ∅, `pc := pc + off` if `c ≠ 0`, else `pc + 1`  |
|                | 3  | `–‒`   | HALT       | Stops                                                        |
|                | 4  | `––`   | CALL       | `off` → `pc + 1`, `pc := pc + off`                             |
|                | 5  | `–—`   | RET        | `a` → ∅, `pc := a`                                             |
| 5 `—` I/O      | 0  | `—-`   | READ       | ∅ → `byte`, or `-1` at end of input                           |
|                | 1  | `—‐`   | WRITE      | `v` → ∅, emits byte `v`; fault if `v ∉ 0..=255`           |
| 6 `―` Logic    | 0  | `―-`   | EQ         | `a b` → `1` if `a = b`, else `0`                         |
|                | 1  | `―‐`   | LT         | `a b` → `1` if `a < b`, else `0`                         |
|                | 2  | `―‑`   | GT         | `a b` → `1` if `a > b`, else `0`                         |
|                | 3  | `―‒`   | NOT        | `a` → `1` if `a = 0`, else `0`                           |
| 7 `−` Extended | —  |        |            | No pair assigned                                       |

Jump offsets are in instructions, relative to the index of the jump itself. A jump to `pc + off = len` is a fault like any other address outside the program: a program ends only with `HALT`. `RET` takes an absolute address, and the return address `CALL` leaves is an ordinary value on the stack, so a routine moves it out of the way with `SWAP` and `ROT` to reach its arguments.

There are no constants above 7: they are built with arithmetic. `PUSH 7, DUP, MUL, PUSH 2, MUL, PUSH 6, ADD` makes 104.

To write programs without counting offsets by hand, see [assembly.md](assembly.md).
