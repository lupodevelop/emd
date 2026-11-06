// emd: an esoteric language written only in Unicode dashes.
// Every problem in a source, where the decoder stops at the first.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use emd_core::{Instr, Sym};
use std::fmt;

/// Diagnosis of a raw source.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct Report {
    pub problems: Vec<String>,
    /// Occurrences of each symbol of the alphabet.
    pub histogram: [usize; 8],
}

impl Report {
    pub fn is_healthy(&self) -> bool {
        self.problems.is_empty()
    }
}

impl fmt::Display for Report {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut out = if self.problems.is_empty() {
            String::from("no problems found\n")
        } else {
            format!("{} problem(s):\n", self.problems.len())
        };
        for p in &self.problems {
            out += &format!("  - {p}\n");
        }
        out += "symbols:";
        for (s, n) in Sym::ALL.iter().zip(self.histogram) {
            out += &format!("  {s} x{n}");
        }
        out.push('\n');
        f.write_str(&out)
    }
}

/// Everything that stops these bytes from decoding.
pub fn doctor(bytes: &[u8]) -> Report {
    let mut report = Report::default();
    if bytes.starts_with(b"\xEF\xBB\xBF") {
        report.problems.push("file starts with a UTF-8 BOM (U+FEFF)".into());
    }
    if let Err(e) = std::str::from_utf8(bytes) {
        report.problems.push(format!("invalid UTF-8 at byte {}", e.valid_up_to()));
    }
    let text = String::from_utf8_lossy(bytes);
    let dashes_and_others = text.chars().filter(|&c| c != '\n').count();
    let mut syms = Vec::new();
    for (number, line) in text.split('\n').enumerate() {
        let length = line.chars().count();
        if length > emd_core::LINE_MAX {
            report.problems.push(format!(
                "line {} has {length} code points, the limit is {}",
                number + 1,
                emd_core::LINE_MAX
            ));
        }
    }
    for (index, ch) in text.chars().enumerate() {
        if ch == '\n' || (index == 0 && ch == '\u{FEFF}') {
            continue;
        }
        match Sym::from_char(ch) {
            Some(s) => {
                report.histogram[usize::from(s.index())] += 1;
                syms.push(s);
            }
            None => {
                let cp = format!("U+{:04X}", ch as u32);
                let what = if ch == '\r' {
                    "carriage return: only U+000A breaks a line".to_string()
                } else if ch.is_whitespace() {
                    "whitespace".to_string()
                } else if let Some(name) = lookalike(ch) {
                    format!("{name}: looks like a dash, is not one of the eight")
                } else if is_invisible(ch) {
                    "invisible character".to_string()
                } else if ch == char::REPLACEMENT_CHARACTER {
                    "undecodable bytes".to_string()
                } else {
                    "not in the alphabet".to_string()
                };
                report.problems.push(format!("code point {index}: {cp} {what}"));
            }
        }
    }
    if report.histogram.iter().sum::<usize>() == dashes_and_others && !dashes_and_others.is_multiple_of(2) {
        report.problems.push(format!("odd number of code points ({dashes_and_others})"));
    }
    if syms.len() == dashes_and_others {
        for (i, &[f, o]) in syms.as_chunks::<2>().0.iter().enumerate() {
            if Instr::decode(f, o).is_none() {
                report.problems.push(format!("instruction {i}: pair {f} {o} is unassigned"));
            }
        }
    }
    report
}

fn lookalike(ch: char) -> Option<&'static str> {
    Some(match ch {
        '\u{00AD}' => "SOFT HYPHEN",
        '\u{00AF}' => "MACRON",
        '\u{02D7}' => "MODIFIER LETTER MINUS SIGN",
        '\u{058A}' => "ARMENIAN HYPHEN",
        '\u{05BE}' => "HEBREW PUNCTUATION MAQAF",
        '\u{1400}' => "CANADIAN SYLLABICS HYPHEN",
        '\u{1806}' => "MONGOLIAN TODO SOFT HYPHEN",
        '\u{2043}' => "HYPHEN BULLET",
        '\u{2053}' => "SWUNG DASH",
        '\u{203E}' => "OVERLINE",
        '\u{207B}' => "SUPERSCRIPT MINUS",
        '\u{208B}' => "SUBSCRIPT MINUS",
        '\u{2500}' => "BOX DRAWINGS LIGHT HORIZONTAL",
        '\u{2501}' => "BOX DRAWINGS HEAVY HORIZONTAL",
        '\u{2796}' => "HEAVY MINUS SIGN",
        '\u{2E17}' => "DOUBLE OBLIQUE HYPHEN",
        '\u{2E3A}' => "TWO-EM DASH",
        '\u{2E3B}' => "THREE-EM DASH",
        '\u{2E40}' => "DOUBLE HYPHEN",
        '\u{2E5D}' => "OBLIQUE HYPHEN",
        '\u{301C}' => "WAVE DASH",
        '\u{3030}' => "WAVY DASH",
        '\u{30A0}' => "KATAKANA-HIRAGANA DOUBLE HYPHEN",
        '\u{30FC}' => "KATAKANA-HIRAGANA PROLONGED SOUND MARK",
        '\u{FE31}' => "PRESENTATION FORM FOR VERTICAL EM DASH",
        '\u{FE32}' => "PRESENTATION FORM FOR VERTICAL EN DASH",
        '\u{FE58}' => "SMALL EM DASH",
        '\u{FE63}' => "SMALL HYPHEN-MINUS",
        '\u{FF0D}' => "FULLWIDTH HYPHEN-MINUS",
        '\u{FFE3}' => "FULLWIDTH MACRON",
        '\u{10EAD}' => "YEZIDI HYPHENATION MARK",
        _ => return None,
    })
}

fn is_invisible(ch: char) -> bool {
    matches!(
        ch,
        '\u{034F}'
            | '\u{061C}'
            | '\u{180E}'
            | '\u{200B}'..='\u{200F}'
            | '\u{202A}'..='\u{202E}'
            | '\u{2060}'..='\u{2064}'
            | '\u{2066}'..='\u{2069}'
            | '\u{FE00}'..='\u{FE0F}'
            | '\u{FEFF}'
    ) || ch.is_control()
}

#[cfg(test)]
mod tests {
    use super::*;

    const EXAMPLE: &str = "-\u{2010}-\u{2011}\u{2011}-\u{2013}\u{2012}";

    fn xorshift(state: &mut u64) -> u64 {
        *state ^= *state << 13;
        *state ^= *state >> 7;
        *state ^= *state << 17;
        *state
    }

    #[test]
    fn doctor_healthy() {
        let r = doctor(EXAMPLE.as_bytes());
        assert!(r.is_healthy(), "{r}");
        assert_eq!(r.histogram, [3, 1, 2, 1, 1, 0, 0, 0]);
    }

    #[test]
    fn doctor_finds_problems() {
        assert!(doctor(format!("{EXAMPLE}\n").as_bytes()).is_healthy());
        assert!(
            doctor(format!("-\n\u{2010}\n\n{EXAMPLE}\n").as_bytes()).is_healthy(),
            "a pair may cross a line"
        );

        let r = doctor(format!("{EXAMPLE}\r\n").as_bytes());
        assert_eq!(r.problems.len(), 1, "{r}");
        assert!(r.problems[0].contains("carriage return"), "{r}");

        assert!(doctor("-".repeat(32).as_bytes()).is_healthy(), "the limit itself is fine");
        let r = doctor("-".repeat(33).as_bytes());
        assert!(r.problems.iter().any(|p| p.contains("line 1 has 33 code points")), "{r}");
        let r = doctor("-".repeat(34).as_bytes());
        assert_eq!(r.problems.len(), 1, "{r}");
        assert!(r.problems[0].contains("line 1 has 34 code points, the limit is 32"), "{r}");

        // Names from the Unicode database, written out here apart from the table they check.
        for (ch, name) in [
            ('\u{00AD}', "SOFT HYPHEN"),
            ('\u{00AF}', "MACRON"),
            ('\u{02D7}', "MODIFIER LETTER MINUS SIGN"),
            ('\u{058A}', "ARMENIAN HYPHEN"),
            ('\u{05BE}', "HEBREW PUNCTUATION MAQAF"),
            ('\u{1400}', "CANADIAN SYLLABICS HYPHEN"),
            ('\u{1806}', "MONGOLIAN TODO SOFT HYPHEN"),
            ('\u{2043}', "HYPHEN BULLET"),
            ('\u{2053}', "SWUNG DASH"),
            ('\u{203E}', "OVERLINE"),
            ('\u{207B}', "SUPERSCRIPT MINUS"),
            ('\u{208B}', "SUBSCRIPT MINUS"),
            ('\u{2500}', "BOX DRAWINGS LIGHT HORIZONTAL"),
            ('\u{2501}', "BOX DRAWINGS HEAVY HORIZONTAL"),
            ('\u{2796}', "HEAVY MINUS SIGN"),
            ('\u{2E17}', "DOUBLE OBLIQUE HYPHEN"),
            ('\u{2E3A}', "TWO-EM DASH"),
            ('\u{2E3B}', "THREE-EM DASH"),
            ('\u{2E40}', "DOUBLE HYPHEN"),
            ('\u{2E5D}', "OBLIQUE HYPHEN"),
            ('\u{301C}', "WAVE DASH"),
            ('\u{3030}', "WAVY DASH"),
            ('\u{30A0}', "KATAKANA-HIRAGANA DOUBLE HYPHEN"),
            ('\u{30FC}', "KATAKANA-HIRAGANA PROLONGED SOUND MARK"),
            ('\u{FE31}', "PRESENTATION FORM FOR VERTICAL EM DASH"),
            ('\u{FE32}', "PRESENTATION FORM FOR VERTICAL EN DASH"),
            ('\u{FE58}', "SMALL EM DASH"),
            ('\u{FE63}', "SMALL HYPHEN-MINUS"),
            ('\u{FF0D}', "FULLWIDTH HYPHEN-MINUS"),
            ('\u{FFE3}', "FULLWIDTH MACRON"),
            ('\u{10EAD}', "YEZIDI HYPHENATION MARK"),
        ] {
            let r = doctor(format!("-{ch}").as_bytes());
            assert!(r.problems[0].contains(name), "{r}");
        }

        let r = doctor("-\u{200B}-".as_bytes());
        assert!(r.problems[0].contains("invisible"), "{r}");

        let r = doctor("---".as_bytes());
        assert!(r.problems[0].contains("odd"), "{r}");

        let r = doctor("--\u{2212}-".as_bytes());
        assert!(r.problems[0].contains("unassigned"), "{r}");

        let r = doctor(b"\xEF\xBB\xBF--");
        assert_eq!(r.problems.len(), 1, "{r}");
        assert!(r.problems[0].contains("BOM"), "{r}");

        let r = doctor(b"--\xff");
        assert!(r.problems[0].contains("invalid UTF-8"), "{r}");
    }

    /// `doctor` finds a problem exactly when the parser rejects the file.
    #[test]
    fn doctor_agrees_with_parser() {
        let pool: Vec<&[u8]> = vec![
            "-".as_bytes(),
            "\u{2010}".as_bytes(),
            "\u{2011}".as_bytes(),
            "\u{2012}".as_bytes(),
            "\u{2013}".as_bytes(),
            "\u{2014}".as_bytes(),
            "\u{2015}".as_bytes(),
            "\u{2212}".as_bytes(),
            b"\n",
            b" ",
            b"a",
            "\u{FE58}".as_bytes(),
            "\u{200B}".as_bytes(),
            "\u{FEFF}".as_bytes(),
            "\u{00AD}".as_bytes(),
            b"\xff",
            b"\xe2\x80",
        ];
        let mut s = 0x0123_4567_89AB_CDEF_u64;
        let (mut ok, mut bad) = (0, 0);
        for _ in 0..3000 {
            let len = (xorshift(&mut s) % 12) as usize;
            let mut bytes = Vec::new();
            for _ in 0..len {
                // Favors the alphabet, or almost no file would be valid.
                let r = xorshift(&mut s);
                let i = if r.is_multiple_of(4) { 8 + (r / 4 % 9) as usize } else { (r / 4 % 8) as usize };
                bytes.extend_from_slice(pool[i]);
            }
            let report = doctor(&bytes);
            let parsed = crate::parse_bytes(&bytes);
            assert_eq!(report.is_healthy(), parsed.is_ok(), "{bytes:?}\n{report}\n{parsed:?}");
            if parsed.is_ok() { ok += 1 } else { bad += 1 }
        }
        assert!(ok > 100 && bad > 100, "ok={ok} bad={bad}");
    }
}
