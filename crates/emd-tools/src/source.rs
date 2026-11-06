// emd: an esoteric language written only in Unicode dashes.
// Source text to canonical source: from typed letters, and from any layout.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use emd_core::Sym;

/// Text that is not what the command takes. `index` counts code points from 0.
#[derive(Debug, PartialEq, Eq)]
pub enum SourceError {
    NotAKey { index: usize, found: char },
    NotADash { index: usize, found: char },
}

impl std::fmt::Display for SourceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SourceError::NotAKey { index, found } => {
                write!(f, "character {index}: `{found}` is not one of asdfghjk")
            }
            SourceError::NotADash { index, found } => {
                write!(f, "code point {index} is U+{:04X}, not one of the eight dashes", *found as u32)
            }
        }
    }
}

impl std::error::Error for SourceError {}

/// Dashes for text typed with [`emd_core::KEYS`]. Whitespace is dropped, anything else is an error.
pub fn keys(text: &str) -> Result<String, SourceError> {
    let mut out = String::new();
    for (index, c) in text.chars().enumerate() {
        match Sym::from_key(c) {
            Some(s) => out.push(s.to_char()),
            None if c.is_whitespace() => {}
            None => return Err(SourceError::NotAKey { index, found: c }),
        }
    }
    Ok(emd_core::wrap_source(&out))
}

/// The canonical layout of a source, decodable or not. Only dashes and newlines go in.
pub fn fmt(text: &str) -> Result<String, SourceError> {
    let mut dashes = String::with_capacity(text.len());
    for (index, c) in text.chars().enumerate() {
        match c {
            '\n' => {}
            c if Sym::from_char(c).is_some() => dashes.push(c),
            c => {
                return Err(SourceError::NotADash { index, found: c });
            }
        }
    }
    Ok(emd_core::wrap_source(&dashes))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn keys_type_the_alphabet_in_order() {
        assert_eq!(keys("as df\ngh jk\n").unwrap(), emd_core::ALPHABET.iter().collect::<String>() + "\n");
        assert_eq!(keys("").unwrap(), "");
        assert_eq!(keys("asx").unwrap_err().to_string(), "character 2: `x` is not one of asdfghjk");
        // A dash is not a key: it would pass through unnoticed otherwise.
        assert!(keys("-").is_err());
    }
}
