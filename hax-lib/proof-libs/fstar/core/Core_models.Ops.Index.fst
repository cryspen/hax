module Core_models.Ops.Index
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::ops::Index`]
class t_Index (v_Self: Type0) (v_Idx: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Output:Type0;
  f_index_pre:v_Self -> v_Idx -> Type0;
  f_index_post:v_Self -> v_Idx -> f_Output -> Type0;
  f_index:x0: v_Self -> x1: v_Idx
    -> Prims.Pure f_Output (f_index_pre x0 x1) (fun result -> f_index_post x0 x1 result)
}

/// See [`std::ops::IndexMut`]
class t_IndexMut (v_Self: Type0) (v_Idx: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:t_Index v_Self v_Idx
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) (v_Idx:Type0) {|i: t_IndexMut v_Self v_Idx|} -> i._super_i0
