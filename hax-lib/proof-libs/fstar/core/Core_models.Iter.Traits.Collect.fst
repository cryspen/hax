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
