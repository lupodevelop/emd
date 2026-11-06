// emd: an esoteric language written only in Unicode dashes.
// The canonical text of a program.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use crate::instr::Instr;

/// The longest line of a source, in code points.
pub const LINE_MAX: usize = 32;

/// The source of a program: only dashes, no separators.
pub fn encode_program(program: &[Instr]) -> String {
    program.iter().map(|i| i.source()).collect()
}

/// Dashes in lines of [`LINE_MAX`], each ended by a newline: the canonical form.
pub fn wrap_source(dashes: &str) -> String {
    let mut out = String::with_capacity(dashes.len() + dashes.len() / LINE_MAX + 1);
    let mut column = 0;
    for c in dashes.chars() {
        out.push(c);
        column += 1;
        if column == LINE_MAX {
            out.push('\n');
            column = 0;
        }
    }
    if column > 0 {
        out.push('\n');
    }
    out
}

/// [`encode_program`] in canonical form.
pub fn format_program(program: &[Instr]) -> String {
    wrap_source(&encode_program(program))
}
