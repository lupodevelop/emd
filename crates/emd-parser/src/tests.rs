// emd: an esoteric language written only in Unicode dashes.
// Tests of the decoder: every error, and properties over random programs.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use super::*;
use emd_core::encode_program;

const EXAMPLE: &str = "-\u{2010}-\u{2011}\u{2011}-\u{2013}\u{2012}";

#[test]
fn spec_example() {
    let p = parse(EXAMPLE).unwrap();
    assert_eq!(p.len(), 4);
    assert_eq!(p.iter().map(ToString::to_string).collect::<Vec<_>>(), ["PUSH 1", "PUSH 2", "ADD", "HALT"]);
}

#[test]
fn round_trip_all_instructions() {
    let all: Vec<Instr> = Instr::all().collect();
    assert_eq!(parse(&emd_core::format_program(&all)).unwrap(), all);
}

#[test]
fn newlines_go_wherever_they_fall() {
    let want = parse(EXAMPLE).unwrap();
    assert_eq!(parse(&format!("{EXAMPLE}\n")).unwrap(), want);
    let chars: Vec<char> = EXAMPLE.chars().collect();
    for cut in 0..=chars.len() {
        let (a, b): (String, String) = (chars[..cut].iter().collect(), chars[cut..].iter().collect());
        assert_eq!(parse(&format!("{a}\n{b}")).unwrap(), want, "break at {cut}");
        assert_eq!(parse(&format!("\n\n{a}\n\n{b}\n")).unwrap(), want, "blank lines");
    }
    assert_eq!(parse("\n\n").unwrap(), []);
}

#[test]
fn only_the_newline_is_a_line_break() {
    let foreign = |src: &str, ch, index| assert_eq!(parse(src), Err(ParseError::Foreign { index, ch }));
    foreign("--\r\n", '\r', 2);
    foreign("-- ", ' ', 2);
    foreign("-\n-\u{2028}", '\u{2028}', 3);
}

#[test]
fn the_line_limit_counts_code_points_per_line() {
    let long = "-".repeat(LINE_MAX);
    assert!(parse(&long).is_ok(), "the limit itself is allowed, even with no newline");
    assert_eq!(parse(&format!("{long}-")), Err(ParseError::LineTooLong { line: 1 }));
    assert_eq!(parse(&format!("--\n{long}--")), Err(ParseError::LineTooLong { line: 2 }));
    assert!(parse(&format!("{long}\n{long}\n--")).is_ok());
    // Bytes do not count: an em dash is three bytes and one code point.
    assert!(parse(&"\u{2010}-".repeat(LINE_MAX / 2)).is_ok());
}

#[test]
fn any_formatting_gives_the_same_program() {
    let all: Vec<Instr> = Instr::all().collect();
    let program: Vec<Instr> = all.iter().cycle().take(200).copied().collect();
    assert_eq!(parse(&emd_core::format_program(&program)), Ok(program.clone()));
    let formatted = emd_core::format_program(&program);
    assert!(formatted.lines().all(|l| l.chars().count() <= LINE_MAX));
    assert!(formatted.ends_with('\n'));
    assert_eq!(emd_core::format_program(&[]), "");
    // A deliberately odd layout: lines of one, then three, then two, and so on.
    let flat: Vec<char> = encode_program(&program).chars().collect();
    let mut weird = String::new();
    let mut rest = &flat[..];
    for width in [1, 3, 2, LINE_MAX, 5].iter().cycle() {
        if rest.is_empty() {
            break;
        }
        let (head, tail) = rest.split_at((*width).min(rest.len()));
        weird.extend(head);
        weird.push('\n');
        rest = tail;
    }
    assert_eq!(parse(&weird), Ok(program));
}

#[test]
fn lookalike_is_an_error() {
    // U+FE58 SMALL EM DASH is not U+2014.
    assert_eq!(parse("-\u{FE58}"), Err(ParseError::Foreign { index: 1, ch: '\u{FE58}' }));
}

#[test]
fn odd_length() {
    assert_eq!(parse("---"), Err(ParseError::OddLength { code_points: 3 }));
    assert_eq!(parse("-\n--\n"), Err(ParseError::OddLength { code_points: 3 }));
}

#[test]
fn unassigned_pair() {
    let err = parse("--\u{2212}-").unwrap_err();
    assert!(matches!(err, ParseError::Unassigned { index: 1, .. }), "{err}");
}

#[test]
fn invalid_utf8() {
    assert_eq!(parse_bytes(b"--\xff"), Err(ParseError::InvalidUtf8 { offset: 2 }));
}

#[test]
fn empty_program_is_valid_syntax() {
    assert_eq!(parse(""), Ok(vec![]));
}

fn xorshift(state: &mut u64) -> u64 {
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    *state
}

/// Accepted input re-encodes to the same bytes.
#[test]
fn accepted_bytes_are_preserved_exactly() {
    const POOL: [&[u8]; 12] = [
        b"-",
        "\u{2010}".as_bytes(),
        "\u{2011}".as_bytes(),
        "\u{2012}".as_bytes(),
        "\u{2013}".as_bytes(),
        "\u{2014}".as_bytes(),
        "\u{2015}".as_bytes(),
        "\u{2212}".as_bytes(),
        b"\xe2",
        b"\x80",
        b"\n",
        "\u{FE58}".as_bytes(),
    ];
    let mut s = 0x5851_F42D_4C95_7F2D_u64;
    let (mut ok, mut bad) = (0, 0);
    for _ in 0..20_000 {
        let mut bytes = Vec::new();
        for _ in 0..xorshift(&mut s) % 12 {
            // Mostly the alphabet, or almost nothing would be accepted.
            let r = xorshift(&mut s);
            let i = if r.is_multiple_of(16) { 8 + (r / 16 % 4) as usize } else { (r / 16 % 8) as usize };
            bytes.extend_from_slice(POOL[i]);
        }
        match parse_bytes(&bytes) {
            Ok(p) => {
                let dashes: Vec<u8> = bytes.iter().copied().filter(|&b| b != b'\n').collect();
                assert_eq!(encode_program(&p).as_bytes(), &dashes[..]);
                ok += 1;
            }
            Err(_) => bad += 1,
        }
    }
    assert!(ok > 100 && bad > 100, "ok={ok} bad={bad}");
}

#[test]
fn random_programs_round_trip() {
    let all: Vec<Instr> = Instr::all().collect();
    let mut s = 0x2545_F491_4F6C_DD1D_u64;
    for _ in 0..2000 {
        let len = (xorshift(&mut s) % 40) as usize;
        let program: Vec<Instr> =
            (0..len).map(|_| all[(xorshift(&mut s) % all.len() as u64) as usize]).collect();
        let src = emd_core::format_program(&program);
        assert_eq!(src.chars().filter(|&c| c != '\n').count(), 2 * len);
        assert_eq!(parse(&src), Ok(program));
    }
}

#[test]
fn an_unassigned_pair_is_named_in_the_message() {
    let error = parse("\u{2212}-").unwrap_err();
    assert_eq!(error.to_string(), "instruction 0 (U+2212 U+002D) is unassigned");
}
