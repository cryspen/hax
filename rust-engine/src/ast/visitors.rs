//! Provides visitors for our AST.

mod helpers;
mod monoid;

#[allow(missing_docs)]
mod generated {
    use super::helpers::with_span;
    use super::helpers::DiagnosticSet;
    use super::helpers::HandleDiagnostics;
    use super::Monoid;
    use crate::ast::identifiers::*;
    use crate::ast::literals::*;
    use crate::ast::*;
    use std::ops::{Deref, DerefMut};

    include!("visitors/generated.rs");
}

pub use generated::*;
pub use monoid::Monoid;
