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
