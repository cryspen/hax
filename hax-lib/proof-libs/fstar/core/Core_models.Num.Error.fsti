module Core_models.Num.Error
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Core_models.Fmt in
  ()

/// The error type returned when a checked integral type conversion fails.
type t_TryFromIntError = | TryFromIntError : Prims.unit -> t_TryFromIntError

val f_fmt__impl__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl:Core_models.Fmt.t_Display t_TryFromIntError

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_1:Core_models.Error.t_Error t_TryFromIntError

val f_from__impl_2__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_2:Core.Convert.t_From t_TryFromIntError Core_models.Convert.t_Infallible

/// Enum to store the various types of errors that can cause parsing an integer to fail.
/// # Example
/// ```
/// # fn main() {
/// if let Err(e) = i32::from_str_radix("a12", 10) {
///     println!("Failed conversion to i32: {:?}", e.kind());
/// }
/// # }
/// ```
type t_IntErrorKind =
  | IntErrorKind_Empty : t_IntErrorKind
  | IntErrorKind_InvalidDigit : t_IntErrorKind
  | IntErrorKind_PosOverflow : t_IntErrorKind
  | IntErrorKind_NegOverflow : t_IntErrorKind
  | IntErrorKind_Zero : t_IntErrorKind

/// An error which can be returned when parsing an integer.
/// This error is used as the error type for the `from_str_radix()` functions
/// on the primitive integer types, such as [`i8::from_str_radix`].
/// # Potential causes
/// Among other causes, `ParseIntError` can be thrown because of leading or trailing whitespace
/// in the string e.g., when it is obtained from the standard input.
/// Using the [`str::trim()`] method ensures that no whitespace remains before parsing.
/// # Example
/// ```
/// if let Err(e) = i32::from_str_radix("a12", 10) {
///     println!("Failed conversion to i32: {e}");
/// }
/// ```
type t_ParseIntError = { f_kind:t_IntErrorKind }

val t_IntErrorKind_cast_to_repr (x: t_IntErrorKind)
    : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)

/// Outputs the detailed cause of parsing an integer failing.
val impl_ParseIntError__kind (self: t_ParseIntError)
    : Prims.Pure t_IntErrorKind Prims.l_True (fun _ -> Prims.l_True)

val f_fmt__impl_4__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_4:Core_models.Fmt.t_Display t_ParseIntError

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_5:Core_models.Error.t_Error t_ParseIntError
