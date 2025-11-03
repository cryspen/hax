module Core_models.Str.Converts
open Rust_primitives

val from_utf8 (s: t_Slice u8): Core_models.Result.t_Result string Core_models.Str.Error.t_Utf8Error

