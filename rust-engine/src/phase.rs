//! A phase rewrites the AST.

use crate::ast::Item;

// Special kind of unreachability that should be prevented by a phase
macro_rules! unreachable_by_invariant {
    ($phase:ident) => {
        unreachable!(
            "The phase {} should make this unreachable",
            stringify!($phase)
        )
    };
}
pub(crate) use unreachable_by_invariant;

/// Placeholder trait for phases.
pub trait Phase {
    /// Apply the phase on items.
    /// A phase may transform an item into zero, one or more items.
    fn apply(&self, items: &mut Vec<Item>);

    /// This is a compatibility layer for the OCaml engine.
    /// This will be dropped when the OCaml engine is dropped.
    /// Returns `Some` when the phase is actually an OCaml phase.
    /// This is useful for `group_consecutive_ocaml_phases`.
    fn legacy_ocaml_phase(&self) -> Option<&str> {
        None
    }
}

pub mod explicit_monadic;
pub mod legacy;
pub mod reject_not_do_lean_dsl;
