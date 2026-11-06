// emd: an esoteric language written only in Unicode dashes.
// What the `emd` command does with a program, apart from running it.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

mod debug;
mod profile;
mod reduce;
mod slop;
mod source;
mod verify;
mod view;

pub use debug::{Debugger, json_text};
pub use profile::{Profile, profile};
pub use reduce::reduce;
pub use slop::{Slop, slop};
pub use source::{SourceError, fmt, keys};
pub use verify::{VERIFY_STEPS, Verdict, verify};
pub use view::{color, diff, explain, inspect};
