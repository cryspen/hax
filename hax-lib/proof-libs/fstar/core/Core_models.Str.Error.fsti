module Core_models.Str.Error
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Rust_primitives

/// See [`std::str::Utf8Error`]
type t_Utf8Error = | Utf8Error : t_Utf8Error
