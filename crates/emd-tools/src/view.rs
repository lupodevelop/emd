// emd: an esoteric language written only in Unicode dashes.
// Views of a program for people: code points next to dashes, effects, colors, differences.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use emd_core::{Instr, Sym};

/// Table: index, source, code points, mnemonic.
pub fn inspect(program: &[Instr]) -> String {
    let mut out = String::from("  idx  src  code points    instruction\n");
    for (i, instr) in program.iter().enumerate() {
        let (f, o) = instr.encode();
        out += &format!("{i:>5}  {}   {f} {o}  {instr}\n", instr.source());
    }
    out
}

/// Table: index, mnemonic, effect.
pub fn explain(program: &[Instr]) -> String {
    let mut out = String::new();
    for (i, instr) in program.iter().enumerate() {
        out += &format!("{i:>5}  {:<8} {}\n", instr.to_string(), instr.describe());
    }
    out
}

const RAINBOW: [u8; 6] = [31, 33, 32, 36, 34, 35];
const RAINBOW_WIDTH: usize = emd_core::LINE_MAX;

/// One ANSI color per line, by line number only. Takes [`Sym`], so no file byte reaches the terminal.
pub fn color(syms: &[Sym]) -> String {
    let mut out = String::new();
    for (line, chunk) in syms.chunks(RAINBOW_WIDTH).enumerate() {
        out += &format!("\x1b[{}m", RAINBOW[line % RAINBOW.len()]);
        out.extend(chunk.iter().map(|s| s.to_char()));
        out += "\x1b[0m\n";
    }
    out
}

/// Instruction-level diff (LCS), with code points: the dashes look the same.
pub fn diff(a: &[Instr], b: &[Instr]) -> String {
    let (n, m) = (a.len(), b.len());
    let mut lcs = vec![vec![0usize; m + 1]; n + 1];
    for i in (0..n).rev() {
        for j in (0..m).rev() {
            lcs[i][j] = if a[i] == b[j] { lcs[i + 1][j + 1] + 1 } else { lcs[i + 1][j].max(lcs[i][j + 1]) };
        }
    }
    let line = |sign: char, i: Option<usize>, j: Option<usize>, instr: Instr| {
        let (f, o) = instr.encode();
        let idx = |x: Option<usize>| x.map_or("-".to_string(), |x| x.to_string());
        format!("{sign} {:>4} {:>4}  {}  {f} {o}  {instr}\n", idx(i), idx(j), instr.source())
    };
    let mut out = String::from("     a    b  src  code points    instruction\n");
    let (mut i, mut j) = (0, 0);
    let (mut removed, mut added) = (0, 0);
    while i < n || j < m {
        if i < n && j < m && a[i] == b[j] {
            out += &line(' ', Some(i), Some(j), a[i]);
            i += 1;
            j += 1;
        } else if j < m && (i == n || lcs[i][j + 1] >= lcs[i + 1][j]) {
            out += &line('+', None, Some(j), b[j]);
            j += 1;
            added += 1;
        } else {
            out += &line('-', Some(i), None, a[i]);
            i += 1;
            removed += 1;
        }
    }
    if removed + added == 0 {
        out += &format!("identical: {n} instructions\n");
    } else {
        out += &format!("-{removed} +{added}: {n} instructions -> {m}\n");
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn p(src: &str) -> Vec<Instr> {
        src.chars()
            .map(|c| Sym::from_char(c).unwrap())
            .collect::<Vec<_>>()
            .as_chunks::<2>()
            .0
            .iter()
            .map(|&[f, o]| Instr::decode(f, o).unwrap())
            .collect()
    }

    const EXAMPLE: &str = "-\u{2010}-\u{2011}\u{2011}-\u{2013}\u{2012}";

    #[test]
    fn inspect_shows_code_points_and_mnemonics() {
        let s = inspect(&p(EXAMPLE));
        assert!(s.contains("U+002D U+2010  PUSH 1"), "{s}");
        assert!(s.contains("U+2013 U+2012  HALT"), "{s}");
    }

    #[test]
    fn explain_covers_every_instruction() {
        for i in Instr::all() {
            assert!(!i.describe().is_empty());
        }
    }

    #[test]
    fn color_marks_lines_and_nothing_else() {
        let syms = |n: usize, s: u8| vec![Sym::new(s).unwrap(); n];
        let out = color(&syms(70, 5));
        let lines: Vec<&str> = out.lines().collect();
        assert_eq!(lines.len(), 3);
        assert!(lines[0].starts_with("\x1b[31m") && lines[1].starts_with("\x1b[33m"));
        assert!(lines.iter().all(|l| l.ends_with("\x1b[0m")));
        assert_eq!(color(&[]), "");

        // Same length, different symbols: same colors in the same positions.
        let skeleton = |s: String| s.replace(|c| Sym::from_char(c).is_some(), "x");
        assert_eq!(skeleton(color(&syms(70, 0))), skeleton(color(&syms(70, 7))));

        // Without colors and line breaks the source remains, even if undecodable.
        let odd = syms(17, 7);
        let plain: String = color(&odd)
            .replace("\x1b[31m", "")
            .replace("\x1b[33m", "")
            .replace("\x1b[0m", "")
            .replace('\n', "");
        assert_eq!(plain, "\u{2212}".repeat(17));
    }

    #[test]
    fn color_keeps_symbol_order() {
        let source: Vec<Sym> = (0..40).map(|i| Sym::ALL[i % 8]).collect();
        let plain: String = color(&source)
            .split('\x1b')
            .map(|part| part.split_once('m').map_or(part, |(_, rest)| rest))
            .collect::<String>()
            .replace('\n', "");
        let expected: String = source.iter().map(|s| s.to_char()).collect();
        assert_eq!(plain, expected);
    }

    #[test]
    fn diff_marks_changed_instruction() {
        // ADD -> SUB: U+2011 U+002D becomes U+2011 U+2010.
        let a = p(EXAMPLE);
        let b = p("-\u{2010}-\u{2011}\u{2011}\u{2010}\u{2013}\u{2012}");
        let d = diff(&a, &b);
        assert!(d.contains("-    2    -"), "{d}");
        assert!(d.contains("+    -    2"), "{d}");
        assert!(d.contains("U+2011 U+2010  SUB"), "{d}");
        assert!(d.ends_with("-1 +1: 4 instructions -> 4\n"), "{d}");
        assert!(diff(&a, &a).ends_with("identical: 4 instructions\n"));
    }
}

#[cfg(test)]
mod properties {
    use super::*;

    fn xorshift(state: &mut u64) -> u64 {
        *state ^= *state << 13;
        *state ^= *state >> 7;
        *state ^= *state << 17;
        *state
    }

    fn random_program(s: &mut u64, max: u64) -> Vec<Instr> {
        let all: Vec<Instr> = Instr::all().collect();
        (0..xorshift(s) % max).map(|_| all[(xorshift(s) % all.len() as u64) as usize]).collect()
    }

    /// Unchanged and removed lines rebuild `a`; unchanged and added lines rebuild `b`.
    #[test]
    fn diff_rebuilds_both_sides() {
        let mut s = 0x7777_ABAB_1234_5678_u64;
        for _ in 0..3000 {
            let a = random_program(&mut s, 12);
            // Half the time a small edit of `a`: the case a diff exists for.
            let b = if xorshift(&mut s).is_multiple_of(2) {
                let mut b = a.clone();
                if !b.is_empty() {
                    let at = (xorshift(&mut s) % b.len() as u64) as usize;
                    b[at] = Instr::Halt;
                }
                b
            } else {
                random_program(&mut s, 12)
            };
            let text = diff(&a, &b);
            let lines: Vec<&str> = text.lines().collect();
            let body = &lines[1..lines.len() - 1];
            let side = |skip: char| -> Vec<Instr> {
                body.iter()
                    .filter(|l| !l.starts_with(skip))
                    .map(|l| Instr::from_mnemonic(l.rsplit("  ").next().unwrap()).unwrap())
                    .collect()
            };
            assert_eq!(side('+'), a, "{text}");
            assert_eq!(side('-'), b, "{text}");
            assert_eq!(a == b, text.ends_with(&format!("identical: {} instructions\n", a.len())), "{text}");
        }
    }

    /// One line per instruction, with the exact code points.
    #[test]
    fn tables_have_one_line_per_instruction() {
        let mut s = 0x1111_2222_3333_4445_u64;
        for _ in 0..500 {
            let p = random_program(&mut s, 30);
            assert_eq!(explain(&p).lines().count(), p.len());
            let table = inspect(&p);
            assert_eq!(table.lines().count(), p.len() + 1);
            for (line, i) in table.lines().skip(1).zip(&p) {
                let (f, o) = i.encode();
                assert!(line.contains(&format!("{f} {o}  {i}")), "{line}");
                assert!(line.contains(&i.source()), "{line}");
            }
        }
    }
}
