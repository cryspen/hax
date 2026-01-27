module Core_models.Str.Converts
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

val from_utf8 (s: t_Slice u8)
    : Prims.Pure (Core_models.Result.t_Result string Core_models.Str.Error.t_Utf8Error)
      Prims.l_True
      (fun _ -> Prims.l_True)
