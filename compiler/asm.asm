; The emd compiler, written in emd: assembly on stdin, the program in dashes on stdout.
;
;   emd asm compiler/asm.asm > asm.emd           ; built once by the Rust compiler
;   emd run asm.emd < program.asm > program.emd  ; from then on it compiles itself too
;
; It follows crates/emd-asm step by step, so both give the same bytes. On an error it
; prints the line and stops with a division by zero, so `emd run` exits with 1.
; Sources up to 1 MB.

; Variables, one memory cell each.
CONST N 0           ; bytes of input
CONST P 1           ; reading position
CONST LINE 2        ; current line, from 1
CONST LEND 3        ; end of the current line, without its line break
CONST CP 4          ; the code point at P
CONST CPLEN 5       ; its length in bytes
CONST NTOK 6
CONST NSTR 7
CONST NST 8
CONST NCONST 9
CONST NLAB 10
CONST I 11
CONST J 12
CONST K 13
CONST A 14
CONST B 15
CONST C1 16
CONST C2 17
CONST Q1 18
CONST Q2 19
CONST V 20          ; a yes or no answer
CONST VAL 21        ; a value
CONST CVAL 22
CONST W 23
CONST X 24
CONST Y 25
CONST Z 26
CONST T 27
CONST NEG 28
CONST NDIG 29
CONST MORE 30
CONST LO 31
CONST HI 32
CONST TL 33         ; line of the instruction being parsed
CONST CODE 34
CONST CA 35
CONST CB 36
CONST FOUND 37
CONST S 38
CONST PC 39
CONST CHANGED 40
CONST PL 41
CONST LEN 42
CONST PAD 43
CONST OP 44
CONST SYM 45
CONST COL 46
CONST SIG 47        ; digits after the leading zeros
CONST SIGAT 48      ; where they start
CONST BIG 49
CONST DONE 54
CONST TK 50         ; the token last read: kind, line, a, b
CONST TLN 51
CONST TA 52
CONST TB 53
CONST SK 55         ; the statement last read or about to be added
CONST SL 56
CONST SA 57
CONST SB 58
CONST SC 59

CONST MAX 9223372036854775807

; Tables.
CONST SRC 1000000       ; the input, one byte a cell
CONST TOK 2000000       ; tokens, 4 cells each: kind, line, a, b
CONST STR 3000000       ; the bytes of every string
CONST ST 4000000        ; statements, 5 cells each: kind, line, a, b, c
CONST SIZE 5000000
CONST SLOT 6000000
CONST ADDR 7000000
CONST TARGET 8000000    ; the label statement each jump goes to
CONST LABELS 8500000
CONST CONSTS 9000000    ; constants, 3 cells each: name start, name end, value
CONST DIGITS 9500000
CONST MN 10000000       ; instruction names, at MN plus the name in base 27

; Token kinds: 1 word, 2 label, 3 integer, 4 string.
; Statement kinds: 1 label, 2 instruction, 3 push, 4 jump to a label.
; An instruction is family * 8 + operation. The table holds that plus 1,
; and 100, 101, 102 for PUSH, PRINT and CONST.

  PUSH 9 STORE 10003499       ; DUP
  PUSH 10 STORE 10092275      ; DROP
  PUSH 11 STORE 10390787      ; SWAP
  PUSH 12 STORE 10311436      ; OVER
  PUSH 13 STORE 10013547      ; ROT
  PUSH 17 STORE 10000841      ; ADD
  PUSH 18 STORE 10014420      ; SUB
  PUSH 19 STORE 10010056      ; MUL
  PUSH 20 STORE 10003181      ; DIV
  PUSH 21 STORE 10009886      ; MOD
  PUSH 25 STORE 10247162      ; LOAD
  PUSH 26 STORE 20502465      ; STORE
  PUSH 33 STORE 10007657      ; JMP
  PUSH 34 STORE 10000296      ; JZ
  PUSH 35 STORE 10007694      ; JNZ
  PUSH 36 STORE 10158537      ; HALT
  PUSH 37 STORE 10060114      ; CALL
  PUSH 38 STORE 10013277      ; RET
  PUSH 41 STORE 10357970      ; READ
  PUSH 42 STORE 22584543      ; WRITE
  PUSH 49 STORE 10000152      ; EQ
  PUSH 50 STORE 10000344      ; LT
  PUSH 51 STORE 10000209      ; GT
  PUSH 52 STORE 10010631      ; NOT
  PUSH 100 STORE 10330758     ; PUSH
  PUSH 101 STORE 18864309     ; PRINT
  PUSH 102 STORE 11900307     ; CONST

read_input:
  READ DUP PUSH 0 LT JNZ read_done
  LOAD N PUSH SRC ADD STORE
  LOAD N PUSH 1 ADD STORE N
  JMP read_input
read_done:
  DROP
  CALL validate
  CALL lex
  CALL parse
  CALL labels
  CALL layout
  CALL emit
  HALT

; Every routine takes and leaves its values in the cells above. On entry the
; return address is the only thing it may not drop.

fail:         ; prints LINE, then stops with a fault
  PRINT "error at line "
  LOAD LINE STORE VAL
  CALL print_number
  PUSH 10 WRITE
  PUSH 1 PUSH 0 DIV

print_number: ; VAL in decimal
  PUSH 0 STORE NDIG
pn_split:
  LOAD VAL PUSH 10 MOD  LOAD NDIG PUSH DIGITS ADD STORE
  LOAD NDIG PUSH 1 ADD STORE NDIG
  LOAD VAL PUSH 10 DIV DUP STORE VAL
  JNZ pn_split
pn_write:
  LOAD NDIG PUSH 1 SUB DUP STORE NDIG
  PUSH DIGITS ADD LOAD PUSH '0' ADD WRITE
  LOAD NDIG JNZ pn_write
  RET

; Reading: the input must be well-formed UTF-8, as for `emd asm`.

validate:
  PUSH 0 STORE P  PUSH 1 STORE LINE
va_byte:
  LOAD P LOAD N LT JZ va_end
  LOAD P PUSH SRC ADD LOAD STORE X
  LOAD X PUSH 10 EQ JZ va_counted
  LOAD LINE PUSH 1 ADD STORE LINE
va_counted:
  LOAD X PUSH 128 LT JZ va_lead
  LOAD P PUSH 1 ADD STORE P
  JMP va_byte
va_lead:      ; MORE bytes follow: the first in LO..HI, the others in 128..191
  PUSH 128 STORE LO  PUSH 191 STORE HI
  LOAD X PUSH 194 LT JNZ fail
  LOAD X PUSH 224 LT JZ va_three
  PUSH 1 STORE MORE
  JMP va_follow
va_three:
  LOAD X PUSH 240 LT JZ va_four
  PUSH 2 STORE MORE
  LOAD X PUSH 224 EQ JZ va_not_e0
  PUSH 160 STORE LO
va_not_e0:
  LOAD X PUSH 237 EQ JZ va_follow
  PUSH 159 STORE HI
  JMP va_follow
va_four:
  LOAD X PUSH 245 LT JZ fail
  PUSH 3 STORE MORE
  LOAD X PUSH 240 EQ JZ va_not_f0
  PUSH 144 STORE LO
va_not_f0:
  LOAD X PUSH 244 EQ JZ va_follow
  PUSH 143 STORE HI
va_follow:
  LOAD P PUSH 1 ADD STORE P
va_next:
  LOAD MORE JZ va_byte
  LOAD P LOAD N LT JZ fail
  LOAD P PUSH SRC ADD LOAD STORE X
  LOAD X LOAD LO LT JNZ fail
  LOAD HI LOAD X LT JNZ fail
  PUSH 128 STORE LO  PUSH 191 STORE HI
  LOAD P PUSH 1 ADD STORE P
  LOAD MORE PUSH 1 SUB STORE MORE
  JMP va_next
va_end:
  RET

decode:       ; CP and CPLEN: the code point at P
  LOAD P PUSH SRC ADD LOAD STORE X
  LOAD X STORE CP  PUSH 1 STORE CPLEN
  LOAD X PUSH 128 LT JNZ de_end
  LOAD X PUSH 224 LT JZ de_three
  LOAD X PUSH 192 SUB STORE CP  PUSH 2 STORE CPLEN
  JMP de_follow
de_three:
  LOAD X PUSH 240 LT JZ de_four
  LOAD X PUSH 224 SUB STORE CP  PUSH 3 STORE CPLEN
  JMP de_follow
de_four:
  LOAD X PUSH 240 SUB STORE CP  PUSH 4 STORE CPLEN
de_follow:
  PUSH 1 STORE Y
de_next:
  LOAD Y LOAD CPLEN LT JZ de_end
  LOAD CP PUSH 64 MUL
  LOAD P LOAD Y ADD PUSH SRC ADD LOAD PUSH 128 SUB
  ADD STORE CP
  LOAD Y PUSH 1 ADD STORE Y
  JMP de_next
de_end:
  RET

; Lexing, line by line.

lex:
  PUSH 0 STORE P  PUSH 1 STORE LINE
le_line:
  LOAD P LOAD N LT JZ le_end
  LOAD P STORE LEND
le_find:
  LOAD LEND LOAD N LT JZ le_found
  LOAD LEND PUSH SRC ADD LOAD PUSH 10 EQ JNZ le_found
  LOAD LEND PUSH 1 ADD STORE LEND
  JMP le_find
le_found:     ; T: the line break; a carriage return just before it is not in the line
  LOAD LEND STORE T
  LOAD LEND LOAD N LT JZ le_tokens
  LOAD LEND LOAD P GT JZ le_tokens
  LOAD LEND PUSH 1 SUB PUSH SRC ADD LOAD PUSH 13 EQ JZ le_tokens
  LOAD LEND PUSH 1 SUB STORE LEND
le_tokens:
  LOAD P LOAD LEND LT JZ le_next_line
  CALL decode
  LOAD CP PUSH ';' EQ JNZ le_next_line
  CALL space
  LOAD V JZ le_token
  LOAD P LOAD CPLEN ADD STORE P
  JMP le_tokens
le_token:
  CALL token
  JMP le_tokens
le_next_line:
  LOAD T PUSH 1 ADD STORE P
  LOAD LINE PUSH 1 ADD STORE LINE
  JMP le_line
le_end:
  RET

space:        ; V: CP is white space, as Rust's char::is_whitespace says
  PUSH 1 STORE V
  LOAD CP PUSH 32 EQ JNZ sp_end
  LOAD CP PUSH 9 LT JNZ sp_no
  LOAD CP PUSH 14 LT JNZ sp_end
  LOAD CP PUSH 133 EQ JNZ sp_end
  LOAD CP PUSH 160 EQ JNZ sp_end
  LOAD CP PUSH 5760 EQ JNZ sp_end
  LOAD CP PUSH 8192 LT JNZ sp_no
  LOAD CP PUSH 8203 LT JNZ sp_end
  LOAD CP PUSH 8232 EQ JNZ sp_end
  LOAD CP PUSH 8233 EQ JNZ sp_end
  LOAD CP PUSH 8239 EQ JNZ sp_end
  LOAD CP PUSH 8287 EQ JNZ sp_end
  LOAD CP PUSH 12288 EQ JNZ sp_end
sp_no:
  PUSH 0 STORE V
sp_end:
  RET

digit:        ; V: X is 0 to 9
  LOAD X PUSH '0' LT NOT  LOAD X PUSH '9' GT NOT  MUL STORE V
  RET

letter:       ; V: X is a letter or an underscore
  LOAD X PUSH '_' EQ
  LOAD X PUSH 'a' LT NOT  LOAD X PUSH 'z' GT NOT  MUL ADD
  LOAD X PUSH 'A' LT NOT  LOAD X PUSH 'Z' GT NOT  MUL ADD
  STORE V
  RET

token:        ; the token that starts at P with CP
  LOAD CP PUSH '"' EQ JNZ tk_string
  LOAD CP PUSH '\'' EQ JNZ tk_char
  LOAD CP PUSH '-' EQ JNZ tk_int
  LOAD CP STORE X
  CALL digit
  LOAD V JNZ tk_int
  CALL letter
  LOAD V JNZ tk_word
  JMP fail

tk_word:      ; a name, or a label when a colon follows
  LOAD P STORE TA
tw_next:
  LOAD P PUSH 1 ADD STORE P
  LOAD P LOAD LEND LT JZ tw_end
  LOAD P PUSH SRC ADD LOAD STORE X
  CALL letter
  LOAD V JNZ tw_next
  CALL digit
  LOAD V JNZ tw_next
tw_end:
  LOAD P STORE TB  PUSH 1 STORE TK
  LOAD P LOAD LEND LT JZ tok_add
  LOAD P PUSH SRC ADD LOAD PUSH ':' EQ JZ tok_add
  PUSH 2 STORE TK
  LOAD P PUSH 1 ADD STORE P
  JMP tok_add

tk_int:       ; an optional minus, then digits. Past MAX it is marked too big, an error
              ; once used, and past what an i128 holds it is an error at once, as in Rust.
  LOAD CP PUSH '-' EQ STORE NEG
  PUSH 0 STORE VAL  PUSH 0 STORE NDIG  PUSH 0 STORE SIG  PUSH 0 STORE BIG
  LOAD P LOAD NEG ADD STORE P
ti_next:
  LOAD P LOAD LEND LT JZ ti_end
  LOAD P PUSH SRC ADD LOAD STORE X
  CALL digit
  LOAD V JZ ti_end
  LOAD X PUSH '0' SUB STORE Y
  LOAD NDIG PUSH 1 ADD STORE NDIG
  LOAD SIG LOAD Y ADD JZ ti_skip        ; a leading zero
  LOAD SIG JNZ ti_counted
  LOAD P STORE SIGAT
ti_counted:
  LOAD SIG PUSH 1 ADD STORE SIG
  LOAD BIG JNZ ti_skip
  ; VAL * 10 + Y must not pass MAX
  LOAD VAL  PUSH MAX LOAD Y SUB PUSH 10 DIV  GT JZ ti_fits
  PUSH 1 STORE BIG
  JMP ti_skip
ti_fits:
  LOAD VAL PUSH 10 MUL LOAD Y ADD STORE VAL
ti_skip:
  LOAD P PUSH 1 ADD STORE P
  JMP ti_next
ti_end:
  LOAD NDIG JZ fail
  LOAD BIG JZ ti_sign
  LOAD SIG PUSH 39 GT JNZ fail
  LOAD SIG PUSH 39 LT JNZ ti_sign
  ; 39 digits: against 2^127 - 1, or 2^127 after a minus, 13 digits at a time
  LOAD SIGAT STORE Q1  PUSH 0 STORE DONE
  PUSH 1701411834604 CALL i128_part
  PUSH 6923173168730 CALL i128_part
  PUSH 3715884105727 LOAD NEG ADD CALL i128_part
ti_sign:
  LOAD NEG JZ ti_add
  PUSH 0 LOAD VAL SUB STORE VAL
ti_add:
  PUSH 3 STORE TK  LOAD VAL STORE TA  LOAD BIG STORE TB
  JMP tok_add

i128_part:    ; under the return address, 13 digits of the limit; Q1 moves past the next 13
  SWAP STORE C1
  LOAD DONE JNZ ib_skip
  PUSH 0 STORE Z  LOAD Q1 PUSH 13 ADD STORE Q2
ib_digit:
  LOAD Z PUSH 10 MUL  LOAD Q1 PUSH SRC ADD LOAD PUSH '0' SUB  ADD STORE Z
  LOAD Q1 PUSH 1 ADD DUP STORE Q1
  LOAD Q2 LT JNZ ib_digit
  LOAD Z LOAD C1 GT JNZ fail
  LOAD Z LOAD C1 LT STORE DONE
ib_skip:
  RET

tk_char:      ; one character or escape between quotes
  LOAD P PUSH 1 ADD STORE P
  LOAD P LOAD LEND LT JZ fail
  CALL decode
  LOAD P LOAD CPLEN ADD STORE P
  LOAD CP STORE VAL
  LOAD CP PUSH '\\' EQ JZ tc_close
  CALL escape
tc_close:
  LOAD P LOAD LEND LT JZ fail
  LOAD P PUSH SRC ADD LOAD PUSH '\'' EQ JZ fail
  LOAD P PUSH 1 ADD STORE P
  PUSH 3 STORE TK  LOAD VAL STORE TA  PUSH 0 STORE TB
  JMP tok_add

tk_string:    ; bytes up to the closing quote, escapes resolved
  LOAD NSTR STORE TA
  LOAD P PUSH 1 ADD STORE P
ts_next:
  LOAD P LOAD LEND LT JZ fail
  CALL decode
  LOAD CP PUSH '"' EQ JNZ ts_end
  LOAD CP PUSH '\\' EQ JZ ts_raw
  LOAD P PUSH 1 ADD STORE P
  CALL escape
  LOAD VAL  LOAD NSTR PUSH STR ADD STORE
  LOAD NSTR PUSH 1 ADD STORE NSTR
  JMP ts_next
ts_raw:       ; the character's own bytes
  LOAD CPLEN STORE Y
ts_copy:
  LOAD P PUSH SRC ADD LOAD  LOAD NSTR PUSH STR ADD STORE
  LOAD NSTR PUSH 1 ADD STORE NSTR
  LOAD P PUSH 1 ADD STORE P
  LOAD Y PUSH 1 SUB DUP STORE Y
  JNZ ts_copy
  JMP ts_next
ts_end:
  LOAD P PUSH 1 ADD STORE P
  PUSH 4 STORE TK  LOAD NSTR LOAD TA SUB STORE TB
  JMP tok_add

escape:       ; VAL: the character after a backslash at P
  LOAD P LOAD LEND LT JZ fail
  LOAD P PUSH SRC ADD LOAD STORE X
  LOAD P PUSH 1 ADD STORE P
  LOAD X STORE VAL
  LOAD X PUSH '\\' EQ JNZ es_end
  LOAD X PUSH '"' EQ JNZ es_end
  LOAD X PUSH '\'' EQ JNZ es_end
  PUSH 10 STORE VAL  LOAD X PUSH 'n' EQ JNZ es_end
  PUSH 9 STORE VAL   LOAD X PUSH 't' EQ JNZ es_end
  PUSH 13 STORE VAL  LOAD X PUSH 'r' EQ JNZ es_end
  PUSH 0 STORE VAL   LOAD X PUSH '0' EQ JNZ es_end
  JMP fail
es_end:
  RET

tok_add:      ; a token of kind TK with TA and TB, on LINE
  LOAD NTOK PUSH 4 MUL PUSH TOK ADD STORE X
  LOAD TK  LOAD X STORE
  LOAD LINE  LOAD X PUSH 1 ADD STORE
  LOAD TA  LOAD X PUSH 2 ADD STORE
  LOAD TB  LOAD X PUSH 3 ADD STORE
  LOAD NTOK PUSH 1 ADD STORE NTOK
  RET

tok_read:     ; token I into TK, TLN, TA, TB
  LOAD I PUSH 4 MUL PUSH TOK ADD STORE X
  LOAD X LOAD STORE TK
  LOAD X PUSH 1 ADD LOAD STORE TLN
  LOAD X PUSH 2 ADD LOAD STORE TA
  LOAD X PUSH 3 ADD LOAD STORE TB
  RET

; Parsing: tokens to statements, with constants resolved.

parse:
  PUSH 0 STORE I
pa_next:
  LOAD I LOAD NTOK LT JZ pa_end
  CALL tok_read
  LOAD I PUSH 1 ADD STORE I
  LOAD TLN STORE LINE  LOAD TLN STORE TL
  LOAD TA STORE A  LOAD TB STORE B
  LOAD TK PUSH 2 EQ JZ pa_word
  CALL reject_reserved
  PUSH 1 STORE SK  LOAD TL STORE SL  LOAD A STORE SA  LOAD B STORE SB  PUSH 0 STORE SC
  CALL stmt_add
  JMP pa_next
pa_word:
  LOAD TK PUSH 1 EQ JZ fail
  CALL instruction
  JMP pa_next
pa_end:
  RET

instruction:  ; the word A..B starts an instruction on line TL
  CALL mnemonic
  LOAD V STORE CODE
  LOAD CODE JZ fail
  LOAD CODE PUSH 102 EQ JNZ in_const
  LOAD CODE PUSH 100 EQ JNZ in_push
  LOAD CODE PUSH 101 EQ JNZ in_print
  LOAD CODE PUSH 25 EQ JNZ in_memory
  LOAD CODE PUSH 26 EQ JNZ in_memory
  LOAD CODE PUSH 33 EQ JNZ in_jump
  LOAD CODE PUSH 34 EQ JNZ in_jump
  LOAD CODE PUSH 35 EQ JNZ in_jump
  LOAD CODE PUSH 37 EQ JNZ in_jump
in_plain:
  LOAD CODE PUSH 1 SUB STORE SA
  JMP add_instr
in_push:
  CALL value
  LOAD VAL STORE SA
  JMP add_push
in_memory:    ; LOAD x and STORE x push x first
  CALL operand_follows
  LOAD V JZ in_plain
  CALL value
  LOAD VAL STORE SA
  CALL add_push
  JMP in_plain
in_jump:      ; a jump with a label pushes the offset first
  CALL operand_follows
  LOAD V JZ in_plain
  CALL next_token
  LOAD TK PUSH 1 EQ JZ fail
  PUSH 4 STORE SK  LOAD TLN STORE SL  LOAD TA STORE SA  LOAD TB STORE SB
  LOAD CODE PUSH 1 SUB STORE SC
  JMP stmt_add
in_print:     ; PUSH and WRITE for each byte
  CALL next_token
  LOAD TK PUSH 4 EQ JZ fail
  LOAD TA STORE J  LOAD TA LOAD TB ADD STORE K
ip_next:
  LOAD J LOAD K LT JZ ip_end
  LOAD J PUSH STR ADD LOAD STORE SA
  CALL add_push
  PUSH 41 STORE SA
  CALL add_instr
  LOAD J PUSH 1 ADD STORE J
  JMP ip_next
ip_end:
  RET
in_const:     ; a name, then its value
  CALL next_token
  LOAD TK PUSH 1 EQ JZ fail
  LOAD TA STORE A  LOAD TB STORE B
  CALL reject_reserved
  LOAD A STORE CA  LOAD B STORE CB
  CALL value
  LOAD CA STORE A  LOAD CB STORE B
  CALL find_const
  LOAD V JNZ fail
  LOAD NCONST PUSH 3 MUL PUSH CONSTS ADD STORE X
  LOAD CA  LOAD X STORE
  LOAD CB  LOAD X PUSH 1 ADD STORE
  LOAD VAL  LOAD X PUSH 2 ADD STORE
  LOAD NCONST PUSH 1 ADD STORE NCONST
  RET

next_token:   ; the next token, which must be on line TL
  LOAD TL STORE LINE
  LOAD I LOAD NTOK LT JZ fail
  CALL tok_read
  LOAD TLN LOAD TL EQ JZ fail
  LOAD I PUSH 1 ADD STORE I
  RET

operand_follows: ; V: the next token is an integer, or a word that is not an instruction, on line TL
  PUSH 0 STORE V
  LOAD I LOAD NTOK LT JZ of_end
  CALL tok_read
  LOAD TLN LOAD TL EQ JZ of_end
  LOAD TK PUSH 3 EQ JNZ of_yes
  LOAD TK PUSH 1 EQ JZ of_end
  LOAD TA STORE A  LOAD TB STORE B
  CALL mnemonic
  LOAD V NOT STORE V
  RET
of_yes:
  PUSH 1 STORE V
of_end:
  RET

value:        ; VAL: an integer, or a constant defined before
  CALL next_token
  LOAD TK PUSH 3 EQ JZ va_name
  LOAD TB JNZ fail
  LOAD TA STORE VAL
  RET
va_name:
  LOAD TK PUSH 1 EQ JZ fail
  LOAD TA STORE A  LOAD TB STORE B
  CALL find_const
  LOAD V JZ fail
  LOAD CVAL STORE VAL
  RET

reject_reserved: ; the name A..B must not be an instruction
  CALL mnemonic
  LOAD V JNZ fail
  RET

mnemonic:     ; V: the table entry for the name A..B, 0 if it is none
  PUSH 0 STORE W
  LOAD B LOAD A SUB PUSH 5 GT JNZ mn_end
  LOAD A STORE J
mn_next:
  LOAD J LOAD B LT JZ mn_found
  LOAD J PUSH SRC ADD LOAD STORE X
  LOAD X PUSH 'a' LT JNZ mn_upper
  LOAD X PUSH 32 SUB STORE X
mn_upper:
  LOAD X PUSH 'A' LT JNZ mn_none
  LOAD X PUSH 'Z' GT JNZ mn_none
  LOAD W PUSH 27 MUL LOAD X PUSH 64 SUB ADD STORE W
  LOAD J PUSH 1 ADD STORE J
  JMP mn_next
mn_found:
  LOAD W PUSH MN ADD LOAD STORE V
  RET
mn_none:
  PUSH 0 STORE W
mn_end:
  PUSH 0 STORE V
  RET

find_const:   ; V: a constant is named A..B, its value in CVAL
  PUSH 0 STORE K
fc_next:
  LOAD K LOAD NCONST LT JZ fc_none
  LOAD K PUSH 3 MUL PUSH CONSTS ADD STORE X
  LOAD X LOAD STORE C1
  LOAD X PUSH 1 ADD LOAD STORE C2
  LOAD X PUSH 2 ADD LOAD STORE CVAL
  CALL same_name
  LOAD V JNZ fc_end
  LOAD K PUSH 1 ADD STORE K
  JMP fc_next
fc_none:
  PUSH 0 STORE V
fc_end:
  RET

same_name:    ; V: A..B and C1..C2 hold the same bytes
  PUSH 0 STORE V
  LOAD B LOAD A SUB  LOAD C2 LOAD C1 SUB  EQ JZ sn_end
  LOAD A STORE Q1  LOAD C1 STORE Q2
sn_next:
  LOAD Q1 LOAD B LT JZ sn_same
  LOAD Q1 PUSH SRC ADD LOAD  LOAD Q2 PUSH SRC ADD LOAD  EQ JZ sn_end
  LOAD Q1 PUSH 1 ADD STORE Q1  LOAD Q2 PUSH 1 ADD STORE Q2
  JMP sn_next
sn_same:
  PUSH 1 STORE V
sn_end:
  RET

add_instr:    ; instruction SA, on line TL
  PUSH 2 STORE SK
  JMP add_statement
add_push:     ; PUSH of the value SA, on line TL
  PUSH 3 STORE SK
add_statement:
  LOAD TL STORE SL  PUSH 0 STORE SB  PUSH 0 STORE SC
stmt_add:     ; SK, SL, SA, SB, SC as a new statement
  LOAD NST PUSH 5 MUL PUSH ST ADD STORE X
  LOAD SK  LOAD X STORE
  LOAD SL  LOAD X PUSH 1 ADD STORE
  LOAD SA  LOAD X PUSH 2 ADD STORE
  LOAD SB  LOAD X PUSH 3 ADD STORE
  LOAD SC  LOAD X PUSH 4 ADD STORE
  LOAD NST PUSH 1 ADD STORE NST
  RET

stmt_read:    ; statement S into SK, SL, SA, SB, SC
  LOAD S PUSH 5 MUL PUSH ST ADD STORE X
  LOAD X LOAD STORE SK
  LOAD X PUSH 1 ADD LOAD STORE SL
  LOAD X PUSH 2 ADD LOAD STORE SA
  LOAD X PUSH 3 ADD LOAD STORE SB
  LOAD X PUSH 4 ADD LOAD STORE SC
  RET

; Code: labels, the layout of jumps, then the dashes.

labels:       ; every label once, and every jump to a label that exists
  PUSH 0 STORE S
lb_next:
  LOAD S LOAD NST LT JZ lb_jumps
  CALL stmt_read
  LOAD SK PUSH 1 EQ JZ lb_skip
  LOAD SA STORE A  LOAD SB STORE B  LOAD SL STORE LINE
  CALL find_label
  LOAD V JNZ fail
  LOAD S  LOAD NLAB PUSH LABELS ADD STORE
  LOAD NLAB PUSH 1 ADD STORE NLAB
lb_skip:
  LOAD S PUSH 1 ADD STORE S
  JMP lb_next
lb_jumps:
  PUSH 0 STORE S
lj_next:
  LOAD S LOAD NST LT JZ lj_end
  CALL stmt_read
  LOAD SK PUSH 4 EQ JZ lj_skip
  LOAD SA STORE A  LOAD SB STORE B  LOAD SL STORE LINE
  CALL find_label
  LOAD V JZ fail
  LOAD FOUND  LOAD S PUSH TARGET ADD STORE
lj_skip:
  LOAD S PUSH 1 ADD STORE S
  JMP lj_next
lj_end:
  RET

find_label:   ; V: a label is named A..B, its statement in FOUND
  PUSH 0 STORE K
fl_next:
  LOAD K LOAD NLAB LT JZ fl_none
  LOAD K PUSH LABELS ADD LOAD STORE FOUND
  LOAD FOUND PUSH 5 MUL PUSH ST ADD PUSH 2 ADD STORE X
  LOAD X LOAD STORE C1
  LOAD X PUSH 1 ADD LOAD STORE C2
  CALL same_name
  LOAD V JNZ fl_end
  LOAD K PUSH 1 ADD STORE K
  JMP fl_next
fl_none:
  PUSH 0 STORE V
fl_end:
  RET

push_len:     ; LEN: how many instructions push PL. Always odd.
  PUSH 1 STORE LEN
  LOAD PL STORE Z
  LOAD PL PUSH 0 LT JZ pl_next
  PUSH 3 STORE LEN
  PUSH 0 LOAD PL SUB STORE Z
pl_next:
  LOAD Z PUSH 8 LT JNZ pl_end
  LOAD LEN PUSH 4 ADD STORE LEN
  LOAD Z PUSH 7 MOD JNZ pl_down
  LOAD LEN PUSH 2 SUB STORE LEN
pl_down:
  LOAD Z PUSH 7 DIV STORE Z
  JMP pl_next
pl_end:
  RET

offset:       ; PL: the offset jump S needs, counted from the end of its slot
  LOAD S PUSH TARGET ADD LOAD PUSH ADDR ADD LOAD
  LOAD S PUSH ADDR ADD LOAD  LOAD S PUSH SLOT ADD LOAD  ADD
  SUB STORE PL
  RET

layout:       ; a jump's length depends on its offset, and the offset on the jumps
  PUSH 0 STORE S
ly_size:
  LOAD S LOAD NST LT JZ ly_pass
  CALL stmt_read
  PUSH 0 STORE LEN
  LOAD SK PUSH 1 EQ JNZ ly_sized
  PUSH 1 STORE LEN
  LOAD SK PUSH 3 EQ JZ ly_sized
  LOAD SA STORE PL
  CALL push_len
ly_sized:
  LOAD LEN  LOAD S PUSH SIZE ADD STORE
  PUSH 0  LOAD S PUSH SLOT ADD STORE
  LOAD S PUSH 1 ADD STORE S
  JMP ly_size
ly_pass:      ; addresses from the slots, then every slot too small grows
  PUSH 0 STORE PC  PUSH 0 STORE S
ly_address:
  LOAD S LOAD NST LT JZ ly_grow
  LOAD PC  LOAD S PUSH ADDR ADD STORE
  LOAD PC  LOAD S PUSH SIZE ADD LOAD ADD  LOAD S PUSH SLOT ADD LOAD ADD  STORE PC
  LOAD S PUSH 1 ADD STORE S
  JMP ly_address
ly_grow:
  PUSH 0 STORE CHANGED  PUSH 0 STORE S
ly_jump:
  LOAD S LOAD NST LT JZ ly_check
  LOAD S PUSH 5 MUL PUSH ST ADD LOAD PUSH 4 EQ JZ ly_skip
  CALL offset
  CALL push_len
  LOAD LEN  LOAD S PUSH SLOT ADD LOAD  GT JZ ly_skip
  LOAD LEN  LOAD S PUSH SLOT ADD STORE
  PUSH 1 STORE CHANGED
ly_skip:
  LOAD S PUSH 1 ADD STORE S
  JMP ly_jump
ly_check:
  LOAD CHANGED JNZ ly_pass
  RET

emit:
  PUSH 0 STORE COL  PUSH 0 STORE S
em_next:
  LOAD S LOAD NST LT JZ em_end
  CALL stmt_read
  LOAD SK PUSH 2 EQ JZ em_push
  LOAD SA STORE OP
  CALL put
  JMP em_skip
em_push:
  LOAD SK PUSH 3 EQ JZ em_jump
  LOAD SA STORE PL
  CALL put_int
  JMP em_skip
em_jump:
  LOAD SK PUSH 4 EQ JZ em_skip
  CALL offset
  CALL put_int
  CALL push_len
  ; PUSH 0, ADD pairs fill what the offset leaves of the slot
  LOAD S PUSH SLOT ADD LOAD  LOAD LEN SUB PUSH 2 DIV STORE PAD
em_pad:
  LOAD PAD JZ em_instr
  PUSH 0 STORE OP
  CALL put
  PUSH 16 STORE OP
  CALL put
  LOAD PAD PUSH 1 SUB STORE PAD
  JMP em_pad
em_instr:
  LOAD SC STORE OP
  CALL put
em_skip:
  LOAD S PUSH 1 ADD STORE S
  JMP em_next
em_end:
  LOAD COL JZ em_done
  PUSH 10 WRITE
em_done:
  RET

put_int:      ; the instructions that push PL: base 7, and 0 - n when negative
  LOAD PL STORE Z
  LOAD PL PUSH 0 LT JZ pi_split
  PUSH 0 STORE OP
  CALL put
  PUSH 0 LOAD PL SUB STORE Z
pi_split:     ; remainders, lowest first, until what is left is below 8
  PUSH 0 STORE NDIG
pi_next:
  LOAD Z PUSH 8 LT JNZ pi_head
  LOAD Z PUSH 7 MOD  LOAD NDIG PUSH DIGITS ADD STORE
  LOAD NDIG PUSH 1 ADD STORE NDIG
  LOAD Z PUSH 7 DIV STORE Z
  JMP pi_next
pi_head:
  LOAD Z STORE OP
  CALL put
pi_digit:     ; times 7, plus the remainder when it is not 0
  LOAD NDIG JZ pi_sign
  LOAD NDIG PUSH 1 SUB STORE NDIG
  PUSH 7 STORE OP
  CALL put
  PUSH 18 STORE OP
  CALL put
  LOAD NDIG PUSH DIGITS ADD LOAD STORE Z
  LOAD Z JZ pi_digit
  LOAD Z STORE OP
  CALL put
  PUSH 16 STORE OP
  CALL put
  JMP pi_digit
pi_sign:
  LOAD PL PUSH 0 LT JZ pi_end
  PUSH 17 STORE OP
  CALL put
pi_end:
  RET

put:          ; instruction OP as two dashes
  LOAD OP PUSH 8 DIV STORE SYM
  CALL dash
  LOAD OP PUSH 8 MOD STORE SYM
  JMP dash

dash:         ; dash SYM in UTF-8, with a line break after every 32
  LOAD SYM JNZ da_wide
  PUSH '-' WRITE
  JMP da_column
da_wide:
  PUSH 226 WRITE
  LOAD SYM PUSH 7 EQ JNZ da_minus
  PUSH 128 WRITE
  LOAD SYM PUSH 143 ADD WRITE
  JMP da_column
da_minus:
  PUSH 136 WRITE
  PUSH 146 WRITE
da_column:
  LOAD COL PUSH 1 ADD DUP STORE COL
  PUSH 32 EQ JZ da_end
  PUSH 10 WRITE
  PUSH 0 STORE COL
da_end:
  RET
