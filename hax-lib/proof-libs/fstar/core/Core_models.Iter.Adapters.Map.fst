module Core_models.Iter.Adapters.Map
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::iter::Map`]
type t_Map (v_I: Type0) (v_F: Type0) = {
  f_iter:v_I;
  f_f:v_F
}

let impl__new (#v_I #v_F: Type0) (iter: v_I) (f: v_F) : t_Map v_I v_F =
  { f_iter = iter; f_f = f } <: t_Map v_I v_F
