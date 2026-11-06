; FizzBuzz from 1 to 100.
CONST I 0

  PUSH 1 STORE I
next:
  LOAD I PUSH 15 MOD JZ fizzbuzz
  LOAD I PUSH 3 MOD JZ fizz
  LOAD I PUSH 5 MOD JZ buzz
  LOAD I PUSH 10 LT JNZ one_digit
  LOAD I PUSH 10 DIV PUSH '0' ADD WRITE
one_digit:
  LOAD I PUSH 10 MOD PUSH '0' ADD WRITE
  JMP newline
fizzbuzz: PRINT "FizzBuzz"  JMP newline
fizz:     PRINT "Fizz"      JMP newline
buzz:     PRINT "Buzz"
newline:
  PUSH '\n' WRITE
  LOAD I PUSH 100 EQ JNZ done
  LOAD I PUSH 1 ADD STORE I
  JMP next
done:
  HALT
