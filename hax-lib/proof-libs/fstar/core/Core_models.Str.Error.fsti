module Core_models.Str.Error
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::str::Utf8Error`]. The fields are `pub(super)` (private in real
/// `core`) so the model's own tests can build one — `from_utf8` is opaque
/// here, so nothing in the model itself ever populates them.
type t_Utf8Error = {
  f_valid_up_to:usize;
  f_error_len:Core_models.Option.t_Option u8
}

/// Build one from what `rust_primitives::string::str_from_utf8` reports;
/// `error_len == 0` is its encoding of `None`.
val impl_Utf8Error__new (valid_up_to: usize) (error_len: u8)
    : Prims.Pure t_Utf8Error Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::str::Utf8Error::valid_up_to`]
val impl_Utf8Error__valid_up_to (self: t_Utf8Error)
    : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::str::Utf8Error::error_len`]
val impl_Utf8Error__error_len (self: t_Utf8Error)
    : Prims.Pure (Core_models.Option.t_Option usize) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::str::ParseBoolError`]
type t_ParseBoolError = | ParseBoolError : t_ParseBoolError
