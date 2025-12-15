module Core_models.Str.Converts
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

assume
val from_utf8': s: t_Slice u8
  -> Core_models.Result.t_Result string Core_models.Str.Error.t_Utf8Error

unfold
let from_utf8 = from_utf8'
