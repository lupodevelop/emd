# Language specification

An `.emd` file is UTF-8 text. It can hold the eight dashes of the [alphabet](isa.md) and newlines (U+000A). Nothing else: no spaces, no comments, no carriage returns, no BOM.

A line holds at most 32 dashes. All newlines are removed before decoding, so a break can fall anywhere, even inside an instruction, and means nothing. `emd fmt` rewrites a program into full lines of 32.

What remains is read two dashes at a time, and each pair is one instruction. An empty file is a valid program with no instructions. Running it faults at once, because there's nothing to run.

The decoder compares code points. Two dashes that look the same in your font are still two different symbols, and nothing gets normalized or corrected.

## Errors

| Problem                         | Error         | It tells you                        |
| ------------------------------- | ------------- | ----------------------------------- |
| Not valid UTF-8                 | `InvalidUtf8` | The offset of the first bad byte    |
| A character outside the alphabet | `Foreign`    | Its position and value              |
| A line over 32 dashes           | `LineTooLong` | The line number, counting from 1    |
| An odd number of dashes         | `OddLength`   | How many, without newlines          |
| A pair with no instruction      | `Unassigned`  | The instruction index and the pair  |

A carriage return counts as `Foreign`. `emd doctor` explains what's wrong with a file, and `emd fmt` repairs a line that's too long.

Decoding an encoded program gives back the same program. Both models prove it: `decodeProgram_encodeProgram` in Lean, `decode_program_encode_program` in Rocq.

What a program does when it runs is in [semantics.md](semantics.md).
