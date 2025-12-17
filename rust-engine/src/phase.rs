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

/// A Rust phase that operates on the AST.
pub trait Phase {
    /// Apply the phase on items.
    /// A phase may transform an item into zero, one or more items.
    fn apply(&self, items: &mut Vec<Item>);
}

pub mod legacy;

mod explicit_monadic;
mod reject_not_do_lean_dsl;

macro_rules! declare_phase_kind {
    {$($name:ident = $phase:expr),*$(,)?} => {
        /// Enumeration of the available phases.
        #[derive(Clone, Debug, Copy, serde::Serialize, serde::Deserialize)]
        pub enum PhaseKind {
            $(
                #[doc = concat!("The phase [`", stringify!($phase), "].")]
                $name,
            )*
            /// A legacy (OCaml) phase.
            Legacy(crate::phase::legacy::LegacyOCamlPhase),
        }

        impl crate::phase::Phase for PhaseKind {
            fn apply(&self, items: &mut Vec<Item>) {
                match *self {
                    $(Self::$name => $phase.apply(items),)*
                    Self::Legacy(phase) => phase.apply(items),
                }
            }
        }
    };
}

declare_phase_kind! {
    ExplicitMonadic = explicit_monadic::ExplicitMonadic,
    RejectNotDoLeanDSL = reject_not_do_lean_dsl::RejectNotDoLeanDSL,
}
