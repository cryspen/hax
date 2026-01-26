module Core_models.Iter.Traits.Collect
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

class t_IntoIterator (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_IntoIter:Type0;
  f_into_iter_pre:v_Self -> Type0;
  f_into_iter_post:v_Self -> f_IntoIter -> Type0;
  f_into_iter:x0: v_Self
    -> Prims.Pure f_IntoIter (f_into_iter_pre x0) (fun result -> f_into_iter_post x0 result)
}

class t_FromIterator (v_Self: Type0) (v_A: Type0) = {
  f_from_iter_pre:#v_T: Type0 -> {| i1: t_IntoIterator v_T |} -> v_T -> Type0;
  f_from_iter_post:#v_T: Type0 -> {| i1: t_IntoIterator v_T |} -> v_T -> v_Self -> Type0;
  f_from_iter:#v_T: Type0 -> {| i1: t_IntoIterator v_T |} -> x0: v_T
    -> Prims.Pure v_Self
        (f_from_iter_pre #v_T #i1 x0)
        (fun result -> f_from_iter_post #v_T #i1 x0 result)
}
