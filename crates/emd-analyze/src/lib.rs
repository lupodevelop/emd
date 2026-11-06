// emd: an esoteric language written only in Unicode dashes.
// Abstract interpretation: for every input, which instructions run and which faults are ruled out.
// Not analyzed: 64-bit overflow on unknown values, and resource limits.
//
// Author: Daniele Scaratti (lupodevelop)
// License: MIT, see LICENSE

mod analysis;
mod cfg;
mod state;
mod transfer;
mod value;

#[cfg(test)]
mod tests;

pub use analysis::{Analysis, Issue, Kind, analyze};
pub use cfg::cfg;
pub use state::{Cell, Frame, Stacks};
pub use value::Val;
