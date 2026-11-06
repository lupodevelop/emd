// emd: an esoteric language written only in Unicode dashes.
// Bytes decode to a program that encodes back to them without newlines, or fail.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

#![no_main]
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    if let Ok(program) = emd_parser::parse_bytes(data) {
        let symbols: Vec<u8> = data.iter().copied().filter(|b| *b != b'\n').collect();
        assert_eq!(emd_core::encode_program(&program).as_bytes(), symbols);
    }
});
