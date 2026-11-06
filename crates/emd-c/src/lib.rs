// emd: an esoteric language written only in Unicode dashes.
// Programs to C, with the semantics, limits and faults of the VM.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use emd_core::Instr;

const PRELUDE: &str = r#"#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#define MAX_STACK ((size_t)1 << 24)
#define MAX_CELLS ((size_t)1 << 24)

static int64_t *st;
static size_t sp, st_cap;
typedef struct { int64_t key; int64_t value; int used; } Cell;
static Cell *cells;
static size_t cell_count, cell_cap;

static void fault(const char *message) {
  fflush(stdout);
  fprintf(stderr, "fault: %s\n", message);
  exit(1);
}

static void flush_out(void) {
  if (fflush(stdout) == EOF) fault("i/o error");
}

static void room(void) {
  if (sp >= MAX_STACK) fault("stack limit reached");
  if (sp == st_cap) {
    st_cap = st_cap ? st_cap * 2 : 64;
    st = realloc(st, st_cap * sizeof *st);
    if (!st) { fprintf(stderr, "out of memory\n"); exit(2); }
  }
}

static Cell *find(int64_t key) {
  uint64_t h = (uint64_t)key * 0x9E3779B97F4A7C15u;
  for (size_t i = h & (cell_cap - 1);; i = (i + 1) & (cell_cap - 1))
    if (!cells[i].used || cells[i].key == key) return &cells[i];
}

static void grow(void) {
  Cell *old = cells;
  size_t old_cap = cell_cap;
  cell_cap = cell_cap ? cell_cap * 2 : 64;
  cells = calloc(cell_cap, sizeof *cells);
  if (!cells) { fprintf(stderr, "out of memory\n"); exit(2); }
  for (size_t i = 0; i < old_cap; i++)
    if (old[i].used) *find(old[i].key) = old[i];
  free(old);
}

static int64_t load(int64_t key) {
  if (!cell_cap) return 0;
  Cell *c = find(key);
  return c->used ? c->value : 0;
}

static int present(int64_t key) { return cell_cap && find(key)->used; }

static void store(int64_t key, int64_t value) {
  if (cell_count * 2 >= cell_cap) grow();
  Cell *c = find(key);
  if (!c->used) { c->used = 1; c->key = key; cell_count++; }
  c->value = value;
}

static int64_t target(int64_t pc, int64_t offset) {
  int64_t t;
  if (__builtin_add_overflow(pc, offset, &t) || t < 0 || t >= LEN) fault("pc is outside the program");
  return t;
}

#define NEED(n) if (sp < (n)) fault("stack underflow")
#define BINARY(checks, result) NEED(2); { int64_t a = st[sp - 2], b = st[sp - 1], r; checks; r = (result); next = target(pc, 1); sp -= 1; st[sp - 1] = r; }
#define ARITH(builtin) BINARY(if (builtin(a, b, &r)) fault("64-bit overflow"), r)

int main(void) {
  int64_t pc = 0, next = 0;
  for (;;) {
    switch (pc) {
"#;

const POSTLUDE: &str = r#"      default: fault("pc is outside the program");
    }
    pc = next;
  }
}
"#;

fn body(instr: Instr) -> String {
    use Instr::*;
    match instr {
        Push(n) => format!("next = target(pc, 1); room(); st[sp++] = {};", n.index()),
        Dup => "NEED(1); next = target(pc, 1); room(); st[sp] = st[sp - 1]; sp++;".into(),
        Drop => "NEED(1); next = target(pc, 1); sp--;".into(),
        Swap => "NEED(2); next = target(pc, 1); { int64_t t = st[sp - 1]; st[sp - 1] = st[sp - 2]; st[sp - 2] = t; }".into(),
        Over => "NEED(2); next = target(pc, 1); room(); st[sp] = st[sp - 2]; sp++;".into(),
        Rot => "NEED(3); next = target(pc, 1); { int64_t t = st[sp - 3]; st[sp - 3] = st[sp - 2]; st[sp - 2] = st[sp - 1]; st[sp - 1] = t; }".into(),
        Add => "ARITH(__builtin_add_overflow)".into(),
        Sub => "ARITH(__builtin_sub_overflow)".into(),
        Mul => "ARITH(__builtin_mul_overflow)".into(),
        Div => r#"BINARY(if (b == 0) fault("division by zero"); if (a == INT64_MIN && b == -1) fault("64-bit overflow"), a / b)"#.into(),
        // INT64_MIN % -1 is 0 here too, and undefined in C.
        Mod => r#"BINARY(if (b == 0) fault("division by zero"), b == -1 ? 0 : a % b)"#.into(),
        Load => r#"NEED(1); if (st[sp - 1] < 0) fault("negative address"); next = target(pc, 1); st[sp - 1] = load(st[sp - 1]);"#.into(),
        Store => r#"NEED(2); if (st[sp - 1] < 0) fault("negative address"); if (!present(st[sp - 1]) && cell_count >= MAX_CELLS) fault("memory cell limit reached"); next = target(pc, 1); store(st[sp - 1], st[sp - 2]); sp -= 2;"#.into(),
        Jmp => "NEED(1); next = target(pc, st[sp - 1]); sp--;".into(),
        Jz => "NEED(2); next = target(pc, st[sp - 2] == 0 ? st[sp - 1] : 1); sp -= 2;".into(),
        Jnz => "NEED(2); next = target(pc, st[sp - 2] != 0 ? st[sp - 1] : 1); sp -= 2;".into(),
        Halt => "flush_out(); return 0;".into(),
        Call => "NEED(1); next = target(pc, st[sp - 1]); st[sp - 1] = pc + 1;".into(),
        Ret => "NEED(1); next = target(0, st[sp - 1]); sp--;".into(),
        // Flushing first shows a prompt before the program waits, as `emd run` does.
        Read => r#"room(); next = target(pc, 1); { flush_out(); int c = getchar(); if (c == EOF && ferror(stdin)) fault("i/o error"); st[sp++] = c == EOF ? -1 : c; }"#.into(),
        Write => r#"NEED(1); if (st[sp - 1] < 0 || st[sp - 1] > 255) fault("not a byte"); next = target(pc, 1); if (putchar((int)st[--sp]) == EOF) fault("i/o error");"#.into(),
        Eq => "BINARY((void)0, a == b)".into(),
        Lt => "BINARY((void)0, a < b)".into(),
        Gt => "BINARY((void)0, a > b)".into(),
        Not => "NEED(1); next = target(pc, 1); st[sp - 1] = st[sp - 1] == 0;".into(),
    }
}

/// A C program that behaves like `program`.
pub fn to_c(program: &[Instr]) -> String {
    let mut out = format!("#define LEN {}\n{PRELUDE}", program.len());
    for (pc, instr) in program.iter().enumerate() {
        out += &format!("      case {pc}: /* {instr} */ {} break;\n", body(*instr));
    }
    out + POSTLUDE
}
