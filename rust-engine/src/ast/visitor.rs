use super::*;
use std::ops::{Deref, DerefMut};

pub trait Monoid {
    type T;
    fn identity() -> Self::T;
    fn append(left: &mut Self::T, right: Self::T);
}

include!("generated/visitor.rs");

#[allow(unused)]
pub fn visit_expr<V: visitor_map_cf::VisitorMapCf>(
    visitor: &mut V,
    v: &mut Expr,
) -> std::ops::ControlFlow<V::Error, ()> {
    todo!()
}
