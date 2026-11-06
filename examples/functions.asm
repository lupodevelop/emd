; Subroutines: CALL leaves the return address on the stack, RET jumps to it.
; show prints the digit it receives, and a newline.
  PUSH 1 CALL show
  PUSH 2 CALL show
  PUSH 3 CALL show
  HALT
show:
  SWAP PUSH '0' ADD WRITE
  PUSH 10 WRITE
  RET
