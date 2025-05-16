module Core.Str
open Rust_primitives

val impl__str__len: string -> usize
val impl__str__as_bytes: string -> t_Slice u8

/// Parses this string slice into another type
val impl_str__parse (#t: Type0) (#err: Type0) (s:string) :
  (Core.Result.t_Result t err)

/// Trims trailing whitespace
val impl_str__trim : string -> string

/// Split strings on patterns
val impl_str__split : (#pattern: Type) -> string -> pattern ->
(Core.Str.Iter.t_Split pattern)
