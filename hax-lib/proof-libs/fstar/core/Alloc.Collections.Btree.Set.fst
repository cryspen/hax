module Alloc.Collections.Btree.Set
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

assume
val t_BTreeSet': v_T: Type0 -> v_U: Type0 -> eqtype

unfold
let t_BTreeSet (v_T v_U: Type0) = t_BTreeSet' v_T v_U

let impl_11__new (#v_T: Type0) (#v_U: Type0) (_: Prims.unit) : t_BTreeSet v_T v_U =
  BTreeSet (Core_models.Option.Option_None <: Core_models.Option.t_Option v_T)
    (Core_models.Option.Option_None <: Core_models.Option.t_Option v_U)
  <:
  t_BTreeSet v_T v_U
