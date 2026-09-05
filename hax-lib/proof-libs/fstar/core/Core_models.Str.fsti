module Core_models.Str
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Rust_primitives

/// See [`std::primitive::str::len`]
val impl_str__len (s: string) : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)
