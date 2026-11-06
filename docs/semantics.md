# Semantics

Reference models: `formal/lean/Emd.lean` and `formal/rocq/Emd.v`.

## State

$$\Sigma = (pc, S, M, I, O)$$

- `pc`: the index of the current instruction, starting at 0.
- `S`: a stack of integers, empty at the start.
- `M`: memory. Addresses are natural numbers, and every cell is 0 until written.
- `I`: the input bytes not read yet.
- `O`: the bytes written so far.

## A step

Each step runs the instruction at `pc`, with one of three results: the machine continues, `HALT` stops it, or a fault stops it. A fault is an explicit error. There is no undefined behavior.

Every instruction except `HALT` and the jumps moves `pc` forward by one and checks it stays inside the program. So running off the end without a `HALT` is a fault.

## Faults

| Fault             | When                                       |
| ----------------- | ------------------------------------------ |
| `stackUnderflow`  | Not enough values on the stack             |
| `divisionByZero`  | `DIV` or `MOD` with `b = 0`                |
| `negativeAddress` | `LOAD` or `STORE` with an address below 0  |
| `pcOutOfRange`    | A jump or advance outside the program      |
| `invalidByte`     | `WRITE` with a value outside `0..=255`     |

If several apply, an instruction checks the operands first, then their values, then where `pc` goes next.

## Arithmetic

Integers have no bounds in the model. `DIV` truncates toward zero and `MOD` takes the sign of the dividend: `-7 / 2 = -3`, `-7 % 2 = -1`.

## Jumps and calls

An offset counts from the jump itself: `JMP` at index 5 with offset 2 goes to 7, and with offset -5 to 0. `JZ` and `JNZ` pop the offset from the top, then the condition.

`CALL` pops an offset, pushes the index of the next instruction and jumps, so the stack stays the same depth. `RET` pops an absolute address and goes there. The return address is an ordinary value on the stack, so a routine can read it, change it or return somewhere else.

## Input and output

`READ` takes one byte and pushes it as a number from 0 to 255. At end of input it pushes -1 and consumes nothing. `WRITE` pops a value and writes it as a byte.

## Determinism

Each state has at most one next state, so the same program on the same input always does the same thing. `step_det` proves it.

## The Rust VM

`crates/emd-vm` follows the models, with three declared differences:

1. Integers are 64-bit. Overflow is the fault `Overflow`, never a wraparound.
2. It has limits on steps, stack depth and memory cells, and passing one is a fault. By default there is no step limit, and the other two are 2^24.
3. An operating system I/O error is the fault `Io`.

After a fault, the stack, memory and `pc` are as they were before the instruction. How the VM is tied to the models is in [verification.md](verification.md).
