module Core_models.Borrow
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Rust_primitives

/// See [`std::borrow::Borrow`]
class t_Borrow (v_Self: Type0) (v_Borrowed: Type0) = {
  f_borrow_pre:v_Self -> prop;
  f_borrow_post:v_Self -> v_Borrowed -> prop;
  f_borrow:x0: v_Self
    -> Prims.Pure v_Borrowed (f_borrow_pre x0) (fun result -> f_borrow_post x0 result)
}
