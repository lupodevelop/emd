// emd: an esoteric language written only in Unicode dashes.
// Text compiles to a program that decodes back, or reports an error on an existing line.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

#![no_main]
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let Ok(text) = std::str::from_utf8(data) else { return };
    match emd_asm::assemble(text) {
        Ok(program) => {
            assert_eq!(emd_parser::parse(&emd_core::format_program(&program)).unwrap(), program);
        }
        Err(e) => assert!(e.span.line >= 1 && e.span.line <= text.lines().count().max(1) + 1, "{e}"),
    }
});
