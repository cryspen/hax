module Core_models.Str.Error
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::str::Utf8Error`]. Fields are `pub(super)` (private in core) for tests.
type t_Utf8Error = {
  f_valid_up_to:usize;
  f_error_len:Core_models.Option.t_Option u8
}

/// `error_len == 0` encodes `None`.
val impl__new (valid_up_to: usize) (error_len: u8)
    : Prims.Pure t_Utf8Error Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::str::Utf8Error::valid_up_to`]
val impl__valid_up_to (self: t_Utf8Error) : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::str::Utf8Error::error_len`]
val impl__error_len (self: t_Utf8Error)
    : Prims.Pure (Core_models.Option.t_Option usize) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::str::ParseBoolError`]
type t_ParseBoolError = | ParseBoolError : t_ParseBoolError
