module Alloc.Collections.Btree.Set
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

val t_BTreeSet (v_T v_U: Type0) : eqtype

val impl_11__new: #v_T: Type0 -> #v_U: Type0 -> Prims.unit
  -> Prims.Pure (t_BTreeSet v_T v_U) Prims.l_True (fun _ -> Prims.l_True)
