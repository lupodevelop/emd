// emd: an esoteric language written only in Unicode dashes.
// `doctor` finds a problem exactly when the parser rejects the bytes.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

#![no_main]
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let report = emd_parser::doctor(data);
    assert_eq!(report.is_healthy(), emd_parser::parse_bytes(data).is_ok(), "{report}");
});
