; A Brainfuck interpreter in emd. Input: the program, then '!', then its input.
; 8-bit wrapping cells, end of input reads as 0, tape unbounded to the right.
; It cannot fault on any input: moving left of the tape's start ends the program, and
; a program too long for its region stops being read. `emd analyze` proves all of it.
CONST IP 0              ; index of the current Brainfuck instruction
CONST DP 1              ; address of the current tape cell
CONST N 2               ; length of the Brainfuck program
CONST DEPTH 3           ; bracket depth during a scan
CONST CODE 16           ; Brainfuck program, up to TAPE
CONST TAPE 1000000

read_code:
  LOAD N PUSH TAPE PUSH CODE SUB LT NOT JNZ code_full
  READ
  DUP PUSH '!' EQ JNZ code_done
  DUP PUSH 0 LT JNZ code_done
  LOAD N PUSH CODE ADD STORE
  LOAD N PUSH 1 ADD STORE N
  JMP read_code
code_done:
  DROP
code_full:
  PUSH TAPE STORE DP

main:
  LOAD IP LOAD N LT NOT JNZ stop
  LOAD IP PUSH CODE ADD LOAD
  DUP PUSH '>' EQ JNZ op_right
  DUP PUSH '<' EQ JNZ op_left
  DUP PUSH '+' EQ JNZ op_inc
  DUP PUSH '-' EQ JNZ op_dec
  DUP PUSH '.' EQ JNZ op_out
  DUP PUSH ',' EQ JNZ op_in
  DUP PUSH '[' EQ JNZ op_open
  DUP PUSH ']' EQ JNZ op_close
  DROP                  ; anything else is a comment
next:
  LOAD IP PUSH 1 ADD STORE IP
  JMP main

op_right: DROP LOAD DP PUSH 1 ADD STORE DP JMP next
op_left:
  DROP LOAD DP PUSH TAPE GT NOT JNZ stop  ; left of the start ends the program
  LOAD DP PUSH 1 SUB STORE DP JMP next
op_inc:   DROP LOAD DP LOAD PUSH 1 ADD PUSH 256 MOD LOAD DP STORE JMP next
op_dec:   DROP LOAD DP LOAD PUSH 255 ADD PUSH 256 MOD LOAD DP STORE JMP next
op_out:   DROP LOAD DP LOAD WRITE JMP next
op_in:
  DROP READ
  DUP PUSH 0 LT JNZ in_eof
  LOAD DP STORE JMP next
in_eof:
  DROP PUSH 0 LOAD DP STORE JMP next

op_open:
  DROP LOAD DP LOAD JNZ next
  PUSH 1 STORE DEPTH
open_scan:
  LOAD IP PUSH 1 ADD STORE IP
  LOAD IP LOAD N LT NOT JNZ stop        ; unmatched [ ends the program
  LOAD IP PUSH CODE ADD LOAD
  DUP PUSH '[' EQ JNZ open_deeper
  PUSH ']' EQ JNZ open_shallower
  JMP open_scan
open_deeper:
  DROP LOAD DEPTH PUSH 1 ADD STORE DEPTH JMP open_scan
open_shallower:
  LOAD DEPTH PUSH 1 SUB DUP STORE DEPTH JNZ open_scan
  JMP next

op_close:
  DROP LOAD DP LOAD JZ next
  PUSH 1 STORE DEPTH
close_scan:
  LOAD IP PUSH 1 SUB STORE IP
  LOAD IP PUSH 0 LT JNZ stop            ; unmatched ] ends the program
  LOAD IP PUSH CODE ADD LOAD
  DUP PUSH ']' EQ JNZ close_deeper
  PUSH '[' EQ JNZ close_shallower
  JMP close_scan
close_deeper:
  DROP LOAD DEPTH PUSH 1 ADD STORE DEPTH JMP close_scan
close_shallower:
  LOAD DEPTH PUSH 1 SUB DUP STORE DEPTH JNZ close_scan
  JMP next

stop:
  HALT
