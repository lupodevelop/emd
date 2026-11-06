// emd: an esoteric language written only in Unicode dashes.
// `push_int` emits the same bytes as the Lean model. A missing `emdpush` skips; `EMD_REQUIRE_LEAN=1` fails.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use emd_asm::push_int;
use emd_core::encode_program;
use std::path::Path;
use std::process::Command;

#[test]
fn rust_push_int_is_the_proved_mirror() {
    let exe = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../formal/lean/.lake/build/bin/emdpush");
    if !exe.exists() {
        assert!(std::env::var_os("EMD_REQUIRE_LEAN").is_none(), "{} missing", exe.display());
        eprintln!("mirror test skipped: {} missing", exe.display());
        return;
    }
    let mut values: Vec<i64> = (-400..400).collect();
    let mut power = 1i64;
    while let Some(next) = power.checked_mul(7) {
        power = next;
        values.extend([power - 1, power, power + 1, -power - 1, -power, -power + 1]);
    }
    values.extend([i64::MAX, -i64::MAX, i64::MAX - 1, 1 << 62, -(1 << 62)]);
    for value in values {
        let out = Command::new(&exe).arg(value.to_string()).output().unwrap();
        assert!(out.status.success(), "emdpush {value}");
        assert_eq!(
            String::from_utf8(out.stdout).unwrap(),
            encode_program(&push_int(value)),
            "push_int({value})"
        );
    }
}
