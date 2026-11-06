; Copies stdin to stdout until end of input.
loop:
  READ
  DUP PUSH 0 LT JNZ eof     ; READ pushes -1 at end of input
  WRITE
  JMP loop
eof:
  HALT
