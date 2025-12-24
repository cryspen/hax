module Core_models.Str
open Rust_primitives

val impl_str__len: string -> usize
val impl_str__as_bytes: string -> t_Slice u8

