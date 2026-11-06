// emd: an esoteric language written only in Unicode dashes.
// Statements to instructions: integer synthesis and jump layout.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use crate::parser::Statement;
use crate::{AsmError, Located};
use emd_core::{Instr, Sym};
use std::collections::HashMap;

fn lit(n: u8) -> Instr {
    Instr::Push(Sym::new(n).expect("literal below 8"))
}

/// The instructions that push `value`: base 7, and `0 - n` when negative. Never overflows.
pub fn push_int(value: i64) -> Vec<Instr> {
    let mut out = Vec::with_capacity(push_len(value));
    emit_int(value, &mut out);
    out
}

fn emit_int(value: i64, out: &mut Vec<Instr>) {
    if value < 0 {
        out.push(lit(0));
        push_magnitude(value.unsigned_abs(), out);
        out.push(Instr::Sub);
    } else {
        push_magnitude(value.unsigned_abs(), out);
    }
}

fn push_magnitude(n: u64, out: &mut Vec<Instr>) {
    if n < 8 {
        out.push(lit(n as u8));
        return;
    }
    push_magnitude(n / 7, out);
    seven_times_plus(n % 7, out);
}

/// Turns `k` on the stack into `7 * k + digit`.
pub(crate) fn seven_times_plus(digit: u64, out: &mut Vec<Instr>) {
    out.extend([lit(7), Instr::Mul]);
    if digit != 0 {
        out.extend([lit(digit as u8), Instr::Add]);
    }
}

/// `push_int(value).len()`, without building it. Always odd.
pub(crate) fn push_len(value: i64) -> usize {
    let mut len = if value < 0 { 3 } else { 1 };
    let mut n = value.unsigned_abs();
    while n >= 8 {
        len += if n.is_multiple_of(7) { 2 } else { 4 };
        n /= 7;
    }
    len
}

pub fn generate(items: &[Located<Statement<'_>>]) -> Result<Vec<Instr>, AsmError> {
    let labels = resolve_labels(items)?;
    let layout = lay_out(items, &labels);
    Ok(emit(items, &labels, &layout))
}

/// The index of the item each label names.
fn resolve_labels<'a>(items: &[Located<Statement<'a>>]) -> Result<HashMap<&'a str, usize>, AsmError> {
    let mut labels = HashMap::new();
    for (i, item) in items.iter().enumerate() {
        if let Statement::Label(name) = item.value
            && labels.insert(name, i).is_some()
        {
            return Err(AsmError { span: item.span, message: format!("label `{name}` defined twice") });
        }
    }
    for item in items {
        if let Statement::Jump(_, name) = item.value
            && !labels.contains_key(name)
        {
            return Err(AsmError { span: item.span, message: format!("undefined label `{name}`") });
        }
    }
    Ok(labels)
}

/// The instructions before each item, and how many each jump spends on its offset.
pub(crate) struct Layout {
    pub addresses: Vec<i64>,
    pub slots: Vec<usize>,
    pub total: usize,
}

/// An offset's length depends on its value, and its value on the slots it crosses.
/// Slots only grow, until they fit.
fn lay_out(items: &[Located<Statement<'_>>], labels: &HashMap<&str, usize>) -> Layout {
    let sizes: Vec<i64> = items
        .iter()
        .map(|item| match item.value {
            Statement::Label(_) => 0,
            Statement::Instr(_) | Statement::Jump(..) => 1,
            Statement::Push(v) => push_len(v) as i64,
        })
        .collect();
    let jumps: Vec<(usize, usize)> = items
        .iter()
        .enumerate()
        .filter_map(|(i, item)| match item.value {
            Statement::Jump(_, name) => Some((i, labels[name])),
            _ => None,
        })
        .collect();
    fixed_point(&sizes, &jumps)
}

/// The layout for items of these sizes, with jumps from item to item.
pub(crate) fn fixed_point(sizes: &[i64], jumps: &[(usize, usize)]) -> Layout {
    let mut slots = vec![0usize; sizes.len()];
    let mut addresses = vec![0i64; sizes.len()];
    loop {
        let mut pc = 0i64;
        for (i, size) in sizes.iter().enumerate() {
            addresses[i] = pc;
            pc += size + slots[i] as i64;
        }
        let mut changed = false;
        for &(jump, label) in jumps {
            let need = push_len(jump_offset(addresses[label], addresses[jump], slots[jump]));
            if need > slots[jump] {
                slots[jump] = need;
                changed = true;
            }
        }
        if !changed {
            return Layout { addresses, slots, total: pc as usize };
        }
    }
}

fn emit(items: &[Located<Statement<'_>>], labels: &HashMap<&str, usize>, layout: &Layout) -> Vec<Instr> {
    let mut out = Vec::with_capacity(layout.total);
    for (i, item) in items.iter().enumerate() {
        match item.value {
            Statement::Label(_) => {}
            Statement::Instr(instr) => out.push(instr),
            Statement::Push(v) => emit_int(v, &mut out),
            Statement::Jump(instr, name) => {
                let slot = layout.slots[i];
                let offset = jump_offset(layout.addresses[labels[name]], layout.addresses[i], slot);
                emit_int(offset, &mut out);
                pad(slot - push_len(offset), &mut out);
                out.push(instr);
            }
        }
    }
    out
}

/// `extra` no-ops. Always even: `push_len` is odd, and so is every slot.
fn pad(extra: usize, out: &mut Vec<Instr>) {
    debug_assert!(extra.is_multiple_of(2));
    for _ in 0..extra / 2 {
        out.extend([lit(0), Instr::Add]);
    }
}

/// The jump instruction comes after its slot.
fn jump_offset(target: i64, start: i64, slot: usize) -> i64 {
    target - (start + slot as i64)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn push_len_is_the_length_of_push_int() {
        let mut values: Vec<i64> = (-3000..3000).collect();
        let mut power = 1i64;
        while let Some(next) = power.checked_mul(7) {
            power = next;
            values.extend([power - 1, power, power + 1, -power - 1, -power, -power + 1]);
        }
        values.extend([i64::MAX, -i64::MAX]);
        for value in values {
            assert_eq!(push_len(value), push_int(value).len(), "{value}");
        }
    }
}
