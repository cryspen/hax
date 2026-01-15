module Tests.Legacy__attributes.Newtype_pattern
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let v_MAX: usize = mk_usize 10

type t_SafeIndex = { f_i:f_i: usize{b2t (f_i <. v_MAX <: bool)} }

let impl_SafeIndex__new (i: usize) : Core_models.Option.t_Option t_SafeIndex =
  if i <. v_MAX
  then
    Core_models.Option.Option_Some ({ f_i = i } <: t_SafeIndex)
    <:
    Core_models.Option.t_Option t_SafeIndex
  else Core_models.Option.Option_None <: Core_models.Option.t_Option t_SafeIndex

let impl_SafeIndex__as_usize (self: t_SafeIndex) : usize = self.f_i

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1 (#v_T: Type0) : Core_models.Ops.Index.t_Index (t_Array v_T (mk_usize 10)) t_SafeIndex =
  {
    f_Output = v_T;
    f_index_pre = (fun (self: t_Array v_T (mk_usize 10)) (index: t_SafeIndex) -> true);
    f_index_post = (fun (self: t_Array v_T (mk_usize 10)) (index: t_SafeIndex) (out: v_T) -> true);
    f_index = fun (self: t_Array v_T (mk_usize 10)) (index: t_SafeIndex) -> self.[ index.f_i ]
  }
