module Core_models.Ops.Drop
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

class t_Drop (v_Self: Type0) = {
  f_drop_pre:v_Self -> Type0;
  f_drop_post:v_Self -> v_Self -> Type0;
  f_drop:x0: v_Self -> Prims.Pure v_Self (f_drop_pre x0) (fun result -> f_drop_post x0 result)
}
