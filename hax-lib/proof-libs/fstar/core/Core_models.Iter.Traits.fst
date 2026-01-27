module Core_models.Iter.Traits
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

class t_Iterator (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Item:Type0;
  f_next_pre:v_Self -> Type0;
  f_next_post:v_Self -> (v_Self & Core_models.Option.t_Option f_Item) -> Type0;
  f_next:x0: v_Self
    -> Prims.Pure (v_Self & Core_models.Option.t_Option f_Item)
        (f_next_pre x0)
        (fun result -> f_next_post x0 result)
}
