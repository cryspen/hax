//! Trait impls a downstream crate writes for its *own* types.
//!
//! Guards the extra field on `Clone`: aeneas sets `clone_from` in every
//! instance it builds for a crate that is not `core-models` itself, and these
//! impls are what checks that it does. `Eq` carries no such field.

#![allow(dead_code)]

// ----- derived, on a struct --------------------------------------------------

#[derive(Clone, PartialEq, Eq)]
pub struct DerivedStruct {
    a: u8,
    b: bool,
}

pub fn derived_struct_clone(x: &DerivedStruct) -> DerivedStruct {
    x.clone()
}

pub fn derived_struct_eq(x: &DerivedStruct, y: &DerivedStruct) -> bool {
    x == y
}

pub fn derived_struct_ne(x: &DerivedStruct, y: &DerivedStruct) -> bool {
    x != y
}

/// `clone_from` is the provided method, so this is the call that needs the
/// field aeneas may or may not emit.
pub fn derived_struct_clone_from(dst: &mut DerivedStruct, src: &DerivedStruct) {
    dst.clone_from(src)
}

// ----- derived, on an enum --------------------------------------------------

#[derive(Clone, PartialEq, Eq)]
pub enum DerivedEnum {
    Unit,
    Tuple(u16),
    Struct { field: u32 },
}

pub fn derived_enum_clone(x: &DerivedEnum) -> DerivedEnum {
    x.clone()
}

pub fn derived_enum_eq(x: &DerivedEnum, y: &DerivedEnum) -> bool {
    x == y
}

pub fn derived_enum_clone_from(dst: &mut DerivedEnum, src: &DerivedEnum) {
    dst.clone_from(src)
}

// ----- hand-written --------------------------------------------------------

pub struct Manual(u8);

impl Clone for Manual {
    fn clone(&self) -> Manual {
        Manual(self.0)
    }
}

impl PartialEq for Manual {
    fn eq(&self, other: &Manual) -> bool {
        self.0 == other.0
    }
}

impl Eq for Manual {}

// No client-side `Debug` impl: aeneas fails with an internal `Unreachable` on
// any signature mentioning `core::fmt::Formatter`, which it declares as an
// opaque axiom. Unrelated to the `Clone`/`Eq` fields this module guards.

pub fn manual_clone(x: &Manual) -> Manual {
    x.clone()
}

pub fn manual_clone_from(dst: &mut Manual, src: &Manual) {
    dst.clone_from(src)
}

pub fn manual_eq(x: &Manual, y: &Manual) -> bool {
    x == y
}

// ----- generic over the client's own bounds ---------------------------------
//
// A generic function that *passes* the dictionaries on rather than building
// them, which is the other way a client can trip over a changed field list.

pub fn clone_through_bound<T: Clone>(x: &T) -> T {
    x.clone()
}

pub fn eq_through_bound<T: PartialEq>(x: &T, y: &T) -> bool {
    x == y
}

pub fn clone_from_through_bound<T: Clone>(dst: &mut T, src: &T) {
    dst.clone_from(src)
}

// ----- comparing and cloning references -------------------------------------
//
// `impl PartialEq<&B> for &A` and `impl Clone for &T` live in
// `CoreModels/Core/FunsPrologue.lean` rather than in the Rust model; these three
// are what pins the names they have to be published under.

pub fn ref_partial_eq<A: PartialEq<B>, B>(a: &A, b: &B) -> bool {
    core::cmp::PartialEq::eq(&a, &b)
}

pub fn ref_partial_ne<A: PartialEq<B>, B>(a: &A, b: &B) -> bool {
    core::cmp::PartialEq::ne(&a, &b)
}

/// Deliberately not `Clone`, so that `a.clone()` below resolves to
/// `impl Clone for &T` rather than to `T`'s own instance.
pub struct NotClone(pub u8);

pub fn ref_clone(a: &NotClone) -> &NotClone {
    core::clone::Clone::clone(&a)
}
