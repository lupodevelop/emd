// emd: an esoteric language written only in Unicode dashes.
// The files and the terminal the commands work with.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

use emd_core::Instr;
use std::io::{self, Read, Write};

/// Writes to stdout. A closed pipe, as in `emd inspect x | head`, is not an error.
pub fn emit(bytes: &[u8]) -> Result<u8, String> {
    write_to(&mut io::stdout().lock(), bytes)
}

fn write_to(out: &mut impl Write, bytes: &[u8]) -> Result<u8, String> {
    match out.write_all(bytes).and_then(|()| out.flush()) {
        Err(e) if e.kind() != io::ErrorKind::BrokenPipe => Err(e.to_string()),
        _ => Ok(0),
    }
}

/// Flushes stdout. `false` if its reader left: the output has nowhere to go, which is not an error.
pub fn flush() -> Result<bool, String> {
    flush_to(&mut io::stdout())
}

fn flush_to(out: &mut impl Write) -> Result<bool, String> {
    match out.flush() {
        Err(e) if e.kind() == io::ErrorKind::BrokenPipe => Ok(false),
        Err(e) => Err(e.to_string()),
        Ok(()) => Ok(true),
    }
}

/// A line on stderr. `false` if its reader left, as in `emd trace x 2>&1 | head`.
pub fn note(line: &str) -> bool {
    writeln!(io::stderr(), "{line}").is_ok()
}

pub fn read(file: &str) -> Result<Vec<u8>, String> {
    std::fs::read(file).map_err(|e| format!("{file}: {e}"))
}

pub fn load(file: &str) -> Result<Vec<Instr>, String> {
    emd_parser::parse_bytes(&read(file)?).map_err(|e| format!("{file}: {e}"))
}

/// Stdin that flushes stdout first, so a prompt appears before the program waits.
pub struct PromptingStdin;

impl Read for PromptingStdin {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        io::stdout().flush()?;
        io::stdin().read(buf)
    }
}

pub fn text(file: &str) -> Result<String, String> {
    String::from_utf8(read(file)?).map_err(|e| format!("{file}: {e}"))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Stdout whose writes and flushes fail with `kind`.
    struct Failing(io::ErrorKind);

    impl Write for Failing {
        fn write(&mut self, _: &[u8]) -> io::Result<usize> {
            Err(self.0.into())
        }

        fn flush(&mut self) -> io::Result<()> {
            Err(self.0.into())
        }
    }

    #[test]
    fn only_a_closed_pipe_is_not_an_error() {
        assert_eq!(write_to(&mut Failing(io::ErrorKind::BrokenPipe), b"x"), Ok(0));
        assert_eq!(flush_to(&mut Failing(io::ErrorKind::BrokenPipe)), Ok(false));
        assert!(write_to(&mut Failing(io::ErrorKind::StorageFull), b"x").is_err());
        assert!(flush_to(&mut Failing(io::ErrorKind::StorageFull)).is_err());
        assert_eq!(flush_to(&mut Vec::new()), Ok(true));
    }
}
