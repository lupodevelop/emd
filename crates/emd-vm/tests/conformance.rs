// emd: an esoteric language written only in Unicode dashes.
// Each `examples/NAME.emd` with a `tests/conformance/NAME.out` must output exactly that.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use emd_vm::{Limits, Status, Vm};
use std::fs;
use std::path::Path;

#[test]
fn conformance() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut cases = 0;
    for entry in fs::read_dir(root.join("tests/conformance")).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().is_none_or(|e| e != "out") {
            continue;
        }
        let source = root.join("examples").join(path.file_stem().unwrap()).with_extension("emd");
        let name = source.display();
        let program =
            emd_parser::parse_bytes(&fs::read(&source).unwrap()).unwrap_or_else(|e| panic!("{name}: {e}"));
        let input = fs::read(path.with_extension("in")).unwrap_or_default();
        let expected = fs::read(&path).unwrap();
        // Bounded: a bug must fail the test, not hang it.
        let limits = Limits { max_steps: 50_000_000, ..Limits::default() };
        let mut vm = Vm::new(&program, limits);
        let mut out = Vec::new();
        let status = vm.run(&mut input.as_slice(), &mut out).clone();
        assert_eq!(status, Status::Halted, "{name}: pc={} steps={}", vm.pc, vm.steps);
        assert_eq!(out, expected, "{name}");
        cases += 1;
    }
    assert!(cases >= 5, "found only {cases} cases");
}
