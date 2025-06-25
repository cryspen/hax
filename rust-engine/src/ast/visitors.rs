//! Provides visitors for our AST.

mod monoid;

#[allow(missing_docs)]
mod generated {
    use super::Monoid;
    use crate::ast::identifiers::*;
    use crate::ast::literals::*;
    use crate::ast::*;
    use std::ops::{Deref, DerefMut};

    include!("visitors/generated.rs");
}

pub use generated::*;
pub use monoid::Monoid;
