// emd: an esoteric language written only in Unicode dashes.
// Published tables and claims, checked against the code.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use emd_core::{ALPHABET, Instr, KEYS, Sym};
use std::fs;
use std::path::{Path, PathBuf};

fn doc(path: &str) -> String {
    fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join("../..").join(path)).unwrap()
}

fn cells(line: &str) -> Vec<&str> {
    line.split('|').map(str::trim).collect()
}

/// Rows of the form: | 2 | `‑` | U+2011 | ...
fn check_alphabet_table(path: &str) {
    let text = doc(path);
    let mut seen = 0;
    for line in text.lines() {
        let row = cells(line);
        if row.len() < 4 || !row[3].starts_with("U+") {
            continue;
        }
        let index: usize = row[1].parse().unwrap();
        let symbol: Vec<char> = row[2].trim_matches('`').chars().collect();
        assert_eq!(symbol, [ALPHABET[index]], "{path}: {line}");
        assert_eq!(row[3], Sym::ALL[index].to_string(), "{path}: {line}");
        seen += 1;
    }
    assert_eq!(seen, 8, "{path}");
}

#[test]
fn alphabet_tables_match() {
    check_alphabet_table("docs/isa.md");
}

/// Rows of the form: | 2 `‑` Arithmetic | 0 | `‑-` | ADD | ...
#[test]
fn isa_table_matches_every_instruction() {
    let text = doc("docs/isa.md");
    let mut seen = 0;
    for line in text.lines() {
        let row = cells(line);
        if row.len() < 6 || !row[3].starts_with('`') || row[3].contains('·') {
            continue;
        }
        let code = row[3].trim_matches('`');
        let instr = Instr::from_mnemonic(row[4]).unwrap_or_else(|| panic!("{line}"));
        assert_eq!(instr.source(), code, "{line}");
        seen += 1;
    }
    assert_eq!(seen, Instr::all().count() - 8, "PUSH is one row, the others one each");
}

/// The example printed in the README is the real encoding.
#[test]
fn printed_example_is_the_real_program() {
    let source = "-\u{2010}-\u{2011}\u{2011}-\u{2013}\u{2012}";
    assert!(doc("README.md").contains(source));
}

/// `formal/README.md` names real theorems, `docs/verification.md` states real counts, and no proof has a hole.
#[test]
fn verification_claims_match_the_proofs() {
    let lean = [
        "Emd.lean",
        "Emd/Universal.lean",
        "Emd/Lowering.lean",
        "Emd/Properties.lean",
        "Emd/Turing.lean",
        "Emd/Source.lean",
        "Emd/Bounded.lean",
        "Emd/Analyzer.lean",
    ]
    .map(|f| doc(&format!("formal/lean/{f}")))
    .join("\n");
    let rocq =
        ["Emd.v", "Props.v", "Source.v", "Turing.v"].map(|f| doc(&format!("formal/rocq/{f}"))).join("\n");
    let claims = doc("docs/verification.md");
    let names = doc("formal/README.md");

    for (prefix, keyword, proofs) in [("- Lean: ", "theorem", &lean), ("- Rocq: ", "Theorem", &rocq)] {
        let mut named = 0;
        for line in names.lines().filter_map(|l| l.strip_prefix(prefix)) {
            for name in line.split(", ").map(|n| n.trim_matches('`')) {
                assert!(proofs.contains(&format!("{keyword} {name} ")), "{name}");
                named += 1;
            }
        }
        assert!(named >= 7, "{prefix}");
    }

    let count = |text: &str, start: &str| text.lines().filter(|l| l.starts_with(start)).count();
    assert!(claims.contains(&format!("{} Lean theorems", count(&lean, "theorem "))));
    let rocq_count = count(&rocq, "Theorem ") + count(&rocq, "Lemma ");
    assert!(claims.contains(&format!("{rocq_count} Rocq theorems")));

    let vm = doc("crates/emd-vm/src/verification.rs");
    let per_instruction =
        vm.split("macro_rules! harnesses").last().unwrap().split("harnesses! {").next().unwrap();
    let per_instruction = per_instruction.matches("#[kani::proof]").count();
    let vm = vm.split("harnesses! {").last().unwrap();
    let vm = per_instruction * vm.lines().filter(|l| l.contains(": Instr::")).count()
        + vm.matches("#[kani::proof]").count();
    let harnesses = |path: &str| doc(path).matches("#[kani::proof]").count();
    let (core, parser, asm) = (
        harnesses("crates/emd-core/src/verification.rs"),
        harnesses("crates/emd-parser/src/verification.rs"),
        harnesses("crates/emd-asm/src/verification.rs"),
    );
    for n in [core, parser, vm, asm] {
        assert!(claims.contains(&format!("{n}/{n}")), "{n} harnesses");
    }
    assert!(claims.contains(&format!("{} Kani harnesses", core + parser + vm + asm)));

    for hole in ["sorry", "admit", "axiom ", "native_decide"] {
        assert!(!lean.contains(hole), "{hole} in Lean");
    }
    for hole in ["Admitted", "Axiom", "admit"] {
        assert!(!rocq.contains(hole), "{hole} in Rocq");
    }
}

/// Nothing reaches up, and the crates that compute from a program do no I/O.
#[test]
fn crates_stay_layered() {
    let allowed: [(&str, &[&str]); 9] = [
        ("emd-core", &[]),
        ("emd-parser", &["emd-core"]),
        ("emd-vm", &["emd-core"]),
        ("emd-asm", &["emd-core"]),
        ("emd-c", &["emd-core"]),
        ("emd-analyze", &["emd-core"]),
        ("emd-tools", &["emd-core", "emd-vm"]),
        ("emd-wasm", &["emd-core", "emd-parser", "emd-tools", "emd-vm"]),
        ("emd-cli", &["emd-analyze", "emd-asm", "emd-c", "emd-core", "emd-parser", "emd-tools", "emd-vm"]),
    ];
    let crates = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let mut found: Vec<String> =
        fs::read_dir(crates).unwrap().map(|e| e.unwrap().file_name().into_string().unwrap()).collect();
    found.sort_unstable();
    let mut named: Vec<String> = allowed.iter().map(|(name, _)| (*name).to_string()).collect();
    named.sort_unstable();
    assert_eq!(found, named, "a new crate needs its place here");
    for (name, wanted) in allowed {
        let manifest = doc(&format!("crates/{name}/Cargo.toml"));
        let section = manifest.split("[dependencies]").nth(1).unwrap_or("").split("\n[").next().unwrap();
        let mut used: Vec<&str> =
            section.lines().filter_map(|l| l.split(' ').next()).filter(|l| l.starts_with("emd-")).collect();
        used.sort_unstable();
        assert_eq!(used, wanted, "dependencies of {name}");
    }
    for name in ["emd-core", "emd-parser", "emd-asm", "emd-c", "emd-analyze"] {
        for file in rust_files(&Path::new(env!("CARGO_MANIFEST_DIR")).join("..").join(name).join("src")) {
            let stem = file.file_stem().unwrap();
            if stem == "tests" || stem == "verification" || stem == "oracle" {
                continue;
            }
            let text = fs::read_to_string(&file).unwrap();
            let code = text.split("#[cfg(test)]").next().unwrap();
            for io in ["std::fs", "std::io", "std::process", "std::env", "println!", "eprint"] {
                assert!(!code.contains(io), "{io} in {}", file.display());
            }
        }
    }
}

fn rust_files(dir: &Path) -> Vec<PathBuf> {
    let mut found = Vec::new();
    for entry in fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            found.extend(rust_files(&path));
        } else if path.extension().is_some_and(|e| e == "rs") {
            found.push(path);
        }
    }
    found
}

/// Every Rust file says what it is and who wrote it.
#[test]
fn rust_files_have_the_header() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut files = rust_files(&root.join("crates"));
    files.extend(rust_files(&root.join("fuzz/fuzz_targets")));
    assert!(files.len() > 25, "{}", files.len());
    for file in files {
        let text = fs::read_to_string(&file).unwrap();
        let lines: Vec<&str> = text.lines().take_while(|l| l.starts_with("//")).collect();
        assert_eq!(
            lines.first(),
            Some(&"// emd: an esoteric language written only in Unicode dashes."),
            "{}",
            file.display()
        );
        assert!(lines.len() >= 5 && lines[1].len() > 3, "{}: what the file does", file.display());
        assert_eq!(
            lines[lines.len() - 3..],
            ["//", "// Author: Daniele Scaratti (lupodevelop)", "// License: MIT, see LICENSE"],
            "{}",
            file.display()
        );
    }
}

/// The Neovim plugin and the website type dashes from their own tables.
#[test]
fn key_tables_match_the_instructions() {
    let lua = doc("editors/nvim/lua/emd/init.lua");
    let json = doc("website/src/lib/instructions.json");
    let site = doc("website/src/lib/site.ts");
    assert!(lua.contains(&format!("M.keys = \"{}\"", KEYS.iter().collect::<String>())));
    for (i, (key, sym)) in KEYS.iter().zip(Sym::ALL).enumerate() {
        assert_eq!(sym.index() as usize, i);
        assert_eq!(Sym::from_key(*key), Some(sym));
        assert!(lua.contains(&format!("0x{:X}", u32::from(sym.to_char()))), "{sym}");
        let hex = format!("{:04X}", u32::from(sym.to_char()));
        assert!(site.contains(&format!("key: '{key}', code: '{hex}'")), "{sym}");
    }
    for instr in Instr::all() {
        let (f, o) = instr.encode();
        let letters: String = [KEYS[usize::from(f.index())], KEYS[usize::from(o.index())]].iter().collect();
        assert!(lua.contains(&format!("{{ \"{instr}\", \"{letters}\" }}")), "{instr} in the plugin");
        assert!(
            json.contains(&format!("\"name\": \"{instr}\", \"keys\": \"{letters}\"")),
            "{instr} on the website"
        );
    }
}

/// The size of the interpreter the paper cites as its largest example.
/// Checks the published web text, available in every checkout.
#[test]
fn paper_states_the_size_of_the_interpreter() {
    let dashes = doc("examples/brainfuck.emd").chars().filter(|&c| c != '\n').count();
    let claim = format!("Brainfuck interpreter of {} instructions", dashes / 2);
    assert!(doc("website/src/data/paper.json").contains(&claim), "{claim}");
}
