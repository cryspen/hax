module Core_models.Specs.Ops.Range

/// Clients reach `RangeInclusive`'s inherent methods by real core's positional
/// names (`a..=b` is `impl_7__new`), so the model must keep defining them.

open FStar.Mul
open Rust_primitives
open Core_models.Ops.Range

let new_accessors (a b: usize) : Lemma
  (let r = impl_7__new #usize a b in
   impl_7__start #usize r == a /\
   impl_7__end #usize r == b /\
   impl_7__into_inner #usize r == (a, b))
  = ()

let contains (r: t_RangeInclusive usize) (x: usize) : bool = impl_10__contains #usize #usize r x

let is_empty (r: t_RangeInclusive usize) : bool = impl_10__is_empty #usize r

/// A client's generic `r.contains(&x)`, as hax extracts it: F* traits have no
/// provided methods, so this goes through `RangeBoundsDefaults`.
let generic_contains (#r: Type0) {| Core_models.Ops.Range.t_RangeBounds r usize |} (x: r) (i: usize)
    : bool = f_contains #r #usize #FStar.Tactics.Typeclasses.solve #usize x i

let range_contains (r: t_Range usize) (x: usize) : bool = generic_contains r x
