module Core.Str.Iter

/// Split strings on patterns (chars, strings, functions)
[@FStar.Tactics.Typeclasses.tcclass]
type t_Split (pattern: Type)

/// Basic implementations

[@FStar.Tactics.Typeclasses.tcinstance]
val impl_t_split_any (#t:Type): (t_Split Rust_primitives.Char.char)
