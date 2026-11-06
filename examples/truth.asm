; Truth machine: input 0 prints 0 once; input 1 prints 1 forever. No input: stops.
  READ
  DUP PUSH 1 ADD JZ stop
  DUP WRITE
  DUP PUSH '1' EQ JNZ forever
stop:
  HALT
forever:
  DUP WRITE
  JMP forever
