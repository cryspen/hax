module Core_models.Fmt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::fmt::Error`]
type t_Error = | Error : t_Error

val flag_bit (set: bool) (value: u32) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::fmt::Arguments`]
/// The only thing the model records is the "no placeholders" case
/// (`format_args!("a literal")`), which is what [`Arguments::as_str`] observes.
/// Everything else is built by the opaque constructors in [`rt`] and carries no
/// information.
/// The type itself extracts, but Aeneas cannot translate a function that stores
/// a `&'static str` into a struct or reads one back out, so the two functions
/// that touch the payload — and [`write`], which calls `as_str` — are dropped
/// from the Lean extraction.
type t_Arguments =
  | Arguments : Core_models.Option.t_Option string -> Core_models.Marker.t_PhantomData Prims.unit
    -> t_Arguments

/// See [`std::fmt::Arguments::from_str`]
val impl_12__from_str (s: string) : Prims.Pure t_Arguments Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::fmt::Arguments::as_str`]
val impl_12__as_str (self: t_Arguments)
    : Prims.Pure (Core_models.Option.t_Option string) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::fmt::Alignment`]
type t_Alignment =
  | Alignment_Left : t_Alignment
  | Alignment_Right : t_Alignment
  | Alignment_Center : t_Alignment

val t_Alignment_cast_to_repr (x: t_Alignment)
    : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::fmt::Sign`]
type t_Sign =
  | Sign_Plus : t_Sign
  | Sign_Minus : t_Sign

val t_Sign_cast_to_repr (x: t_Sign) : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::fmt::DebugAsHex`]
type t_DebugAsHex =
  | DebugAsHex_Lower : t_DebugAsHex
  | DebugAsHex_Upper : t_DebugAsHex

val t_DebugAsHex_cast_to_repr (x: t_DebugAsHex)
    : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::fmt::FormattingOptions`]
/// Real `core` packs the flags, the fill character, the width and the precision
/// into a `u32` plus two `u16`s. The model keeps the very same information in
/// named fields of primitive type: the getters then transcribe real `core`'s
/// bodies without bit twiddling, and the options can be copied by listing their
/// fields (the model cannot `derive(Copy)`, see [`Formatter::options`]).
/// None of the field names may coincide with a method name of this type — the
/// setters are `width`, `fill`, `align`, … — because Lean derives a projection
/// `FormattingOptions.width` from the field and Aeneas resolves the clash by
/// renaming the *method* to `FormattingOptions.impl.width`. An extracted client
/// calling the setter asks for the unrenamed name and gets the projection. Hence
/// `width_value`, `fill_char`, `align_code`, … here. Same for
/// [`Formatter`]'s single field against [`Formatter::options`].
type t_FormattingOptions = {
  f_sign_plus:bool;
  f_sign_minus:bool;
  f_alternate_flag:bool;
  f_zero_pad_flag:bool;
  f_debug_lower_hex:bool;
  f_debug_upper_hex:bool;
  f_fill_char:FStar.Char.char;
  f_align_code:u8;
  f_width_value:u16;
  f_width_set:bool;
  f_precision_value:u16;
  f_precision_set:bool
}

/// See [`std::fmt::Formatter`]
/// Real `core`'s `Formatter<'a>` also holds the `&'a mut dyn Write` it renders
/// into. The model drops it — nothing is ever rendered (see the module docs) —
/// and keeps only the options, which is what the query methods below observe.
type t_Formatter = { f_formatting_options:t_FormattingOptions }

/// See [`std::fmt::Formatter::with_options`]
val impl_Formatter__with_options (self: t_Formatter) (options: t_FormattingOptions)
    : Prims.Pure (t_Formatter & t_Formatter) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::fmt::Formatter::options`]
val impl_Formatter__options (self: t_Formatter)
    : Prims.Pure t_FormattingOptions Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::fmt::Formatter::write_str`]
val impl_Formatter__write_str (self: t_Formatter) (data: string)
    : Prims.Pure (t_Formatter & Core_models.Result.t_Result Prims.unit t_Error)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// See [`std::fmt::Formatter::write_fmt`]
/// Unlike [`write`] on a caller-provided sink, there is nothing to forward
/// to here: the model's `Formatter` has no sink.
/// The parameter real `core` calls `fmt` is `args` here: a binder named after
/// a module shadows it in the extracted Lean, and `fmt.Error` in this
/// signature would then elaborate as a field projection on the binder.
val impl_Formatter__write_fmt (self: t_Formatter) (args: t_Arguments)
    : Prims.Pure (t_Formatter & Core_models.Result.t_Result Prims.unit t_Error)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// See [`std::fmt::Formatter::pad`]
/// Real `core` truncates `s` to the precision and pads it to the width; the
/// model has nowhere to put the result, so it writes nothing.
val impl_Formatter__pad (self: t_Formatter) (s: string)
    : Prims.Pure (t_Formatter & Core_models.Result.t_Result Prims.unit t_Error)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// See [`std::fmt::Formatter::pad_integral`]
/// Writes nothing, for the same reason as [`Formatter::pad`].
val impl_Formatter__pad_integral (self: t_Formatter) (is_nonnegative: bool) (prefix buf: string)
    : Prims.Pure (t_Formatter & Core_models.Result.t_Result Prims.unit t_Error)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// See [`std::fmt::Formatter::flags`]
/// The six flag bits real `core` keeps at bits 21..27 of its packed `flags`
/// field, shifted down to 0..6 — exactly what real `core` returns.
val impl_Formatter__flags (self: t_Formatter) : Prims.Pure u32 Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::fmt::Formatter::fill`]
val impl_Formatter__fill (self: t_Formatter)
    : Prims.Pure FStar.Char.char Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::fmt::Formatter::sign_plus`]
val impl_Formatter__sign_plus (self: t_Formatter)
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::fmt::Formatter::sign_minus`]
val impl_Formatter__sign_minus (self: t_Formatter)
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::fmt::Formatter::alternate`]
val impl_Formatter__alternate (self: t_Formatter)
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::fmt::Formatter::sign_aware_zero_pad`]
val impl_Formatter__sign_aware_zero_pad (self: t_Formatter)
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::fmt::Display`]
class t_Display (v_Self: Type0) = {
  f_fmt_pre:v_Self -> t_Formatter -> Type0;
  f_fmt_post:v_Self -> t_Formatter -> (t_Formatter & Core_models.Result.t_Result Prims.unit t_Error)
    -> Type0;
  f_fmt:x0: v_Self -> x1: t_Formatter
    -> Prims.Pure (t_Formatter & Core_models.Result.t_Result Prims.unit t_Error)
        (f_fmt_pre x0 x1)
        (fun result -> f_fmt_post x0 x1 result)
}

/// See [`std::fmt::Debug`]
class t_Debug (v_Self: Type0) = {
  f_dbg_fmt_pre:v_Self -> t_Formatter -> Type0;
  f_dbg_fmt_post:
      v_Self ->
      t_Formatter ->
      (t_Formatter & Core_models.Result.t_Result Prims.unit t_Error)
    -> Type0;
  f_dbg_fmt:x0: v_Self -> x1: t_Formatter
    -> Prims.Pure (t_Formatter & Core_models.Result.t_Result Prims.unit t_Error)
        (f_dbg_fmt_pre x0 x1)
        (fun result -> f_dbg_fmt_post x0 x1 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_1 (#v_T: Type0) : t_Debug v_T

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Display_for_u8:t_Display u8

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Display_for_u16:t_Display u16

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Display_for_u32:t_Display u32

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Display_for_u64:t_Display u64

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Display_for_u128:t_Display u128

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Display_for_usize:t_Display usize

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Display_for_i8:t_Display i8

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Display_for_i16:t_Display i16

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Display_for_i32:t_Display i32

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Display_for_i64:t_Display i64

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Display_for_i128:t_Display i128

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Display_for_isize:t_Display isize

val impl_12__write_fmt (f: t_Formatter) (args: t_Arguments)
    : Prims.Pure (t_Formatter & Core_models.Result.t_Result Prims.unit t_Error)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// See [`std::fmt::FormattingOptions::new`]
val impl_FormattingOptions__new: Prims.unit
  -> Prims.Pure t_FormattingOptions Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::fmt::FormattingOptions::get_sign`]
val impl_FormattingOptions__get_sign (self: t_FormattingOptions)
    : Prims.Pure (Core_models.Option.t_Option t_Sign) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::fmt::Formatter::sign`]
val impl_Formatter__sign (self: t_Formatter)
    : Prims.Pure (Core_models.Option.t_Option t_Sign) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::fmt::FormattingOptions::get_sign_aware_zero_pad`]
val impl_FormattingOptions__get_sign_aware_zero_pad (self: t_FormattingOptions)
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::fmt::FormattingOptions::get_alternate`]
val impl_FormattingOptions__get_alternate (self: t_FormattingOptions)
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::fmt::FormattingOptions::get_fill`]
val impl_FormattingOptions__get_fill (self: t_FormattingOptions)
    : Prims.Pure FStar.Char.char Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::fmt::FormattingOptions::get_align`]
val impl_FormattingOptions__get_align (self: t_FormattingOptions)
    : Prims.Pure (Core_models.Option.t_Option t_Alignment) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::fmt::Formatter::align`]
val impl_Formatter__align (self: t_Formatter)
    : Prims.Pure (Core_models.Option.t_Option t_Alignment) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::fmt::FormattingOptions::get_width`]
val impl_FormattingOptions__get_width (self: t_FormattingOptions)
    : Prims.Pure (Core_models.Option.t_Option u16) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::fmt::Formatter::width`]
val impl_Formatter__width (self: t_Formatter)
    : Prims.Pure (Core_models.Option.t_Option usize) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::fmt::FormattingOptions::get_precision`]
val impl_FormattingOptions__get_precision (self: t_FormattingOptions)
    : Prims.Pure (Core_models.Option.t_Option u16) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::fmt::Formatter::precision`]
val impl_Formatter__precision (self: t_Formatter)
    : Prims.Pure (Core_models.Option.t_Option usize) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::fmt::FormattingOptions::get_debug_as_hex`]
val impl_FormattingOptions__get_debug_as_hex (self: t_FormattingOptions)
    : Prims.Pure (Core_models.Option.t_Option t_DebugAsHex) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::fmt::Write`]
class t_Write (v_Self: Type0) = {
  f_write_str_pre:v_Self -> string -> Type0;
  f_write_str_post:v_Self -> string -> (v_Self & Core_models.Result.t_Result Prims.unit t_Error)
    -> Type0;
  f_write_str:x0: v_Self -> x1: string
    -> Prims.Pure (v_Self & Core_models.Result.t_Result Prims.unit t_Error)
        (f_write_str_pre x0 x1)
        (fun result -> f_write_str_post x0 x1 result)
}

/// See [`std::fmt::Formatter::new`]
/// The writer is ignored. It is also generic rather than `dyn Write`: `dyn`
/// has no counterpart in the F* proof libraries.
val impl_Formatter__new
      (#v_W: Type0)
      {| i0: t_Write v_W |}
      (write: v_W)
      (options: t_FormattingOptions)
    : Prims.Pure (v_W & t_Formatter) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::fmt::FormattingOptions::create_formatter`]
/// The writer is ignored and generic, as in [`Formatter::new`].
val impl_FormattingOptions__create_formatter
      (#v_W: Type0)
      {| i0: t_Write v_W |}
      (self: t_FormattingOptions)
      (write: v_W)
    : Prims.Pure (v_W & t_Formatter) Prims.l_True (fun _ -> Prims.l_True)

/// `Write::write_char` and `Write::write_fmt` are trait *defaults* in real
/// `core`, which hax cannot express; like [`crate::cmp::Neq`] for
/// `PartialEq::ne`, they live in a blanket-implemented companion trait.
/// Excluded from the Lean extraction: `write_char` needs
/// `rust_primitives::string::str_of_char`, and the Lean side provides none of
/// the string primitives (`alloc::string` is excluded there for the same
/// reason).
class t_WriteDefaults (v_Self: Type0) = {
  f_write_char_pre:v_Self -> FStar.Char.char -> Type0;
  f_write_char_post:
      v_Self ->
      FStar.Char.char ->
      (v_Self & Core_models.Result.t_Result Prims.unit t_Error)
    -> Type0;
  f_write_char:x0: v_Self -> x1: FStar.Char.char
    -> Prims.Pure (v_Self & Core_models.Result.t_Result Prims.unit t_Error)
        (f_write_char_pre x0 x1)
        (fun result -> f_write_char_post x0 x1 result);
  f_write_fmt_pre:v_Self -> t_Arguments -> Type0;
  f_write_fmt_post:
      v_Self ->
      t_Arguments ->
      (v_Self & Core_models.Result.t_Result Prims.unit t_Error)
    -> Type0;
  f_write_fmt:x0: v_Self -> x1: t_Arguments
    -> Prims.Pure (v_Self & Core_models.Result.t_Result Prims.unit t_Error)
        (f_write_fmt_pre x0 x1)
        (fun result -> f_write_fmt_post x0 x1 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Write_for_Formatter:t_Write t_Formatter

/// See [`std::fmt::write`]
/// Real `core` renders the template and the arguments; the model can only
/// forward the literal case (see [`Arguments`]), and drops the rest. `W`
/// replaces real `core`'s `dyn Write`, as in [`Formatter::new`].
val write (#v_W: Type0) {| i0: t_Write v_W |} (output: v_W) (args: t_Arguments)
    : Prims.Pure (v_W & Core_models.Result.t_Result Prims.unit t_Error)
      Prims.l_True
      (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_14 (#v_W: Type0) {| i0: t_Write v_W |} : t_WriteDefaults v_W

/// See [`std::fmt::Binary`]
class t_Binary (v_Self: Type0) = {
  f_binary_fmt_pre:v_Self -> t_Formatter -> Type0;
  f_binary_fmt_post:
      v_Self ->
      t_Formatter ->
      (t_Formatter & Core_models.Result.t_Result Prims.unit t_Error)
    -> Type0;
  f_binary_fmt:x0: v_Self -> x1: t_Formatter
    -> Prims.Pure (t_Formatter & Core_models.Result.t_Result Prims.unit t_Error)
        (f_binary_fmt_pre x0 x1)
        (fun result -> f_binary_fmt_post x0 x1 result)
}

/// See [`std::fmt::Octal`]
class t_Octal (v_Self: Type0) = {
  f_octal_fmt_pre:v_Self -> t_Formatter -> Type0;
  f_octal_fmt_post:
      v_Self ->
      t_Formatter ->
      (t_Formatter & Core_models.Result.t_Result Prims.unit t_Error)
    -> Type0;
  f_octal_fmt:x0: v_Self -> x1: t_Formatter
    -> Prims.Pure (t_Formatter & Core_models.Result.t_Result Prims.unit t_Error)
        (f_octal_fmt_pre x0 x1)
        (fun result -> f_octal_fmt_post x0 x1 result)
}

/// See [`std::fmt::LowerHex`]
class t_LowerHex (v_Self: Type0) = {
  f_lower_hex_fmt_pre:v_Self -> t_Formatter -> Type0;
  f_lower_hex_fmt_post:
      v_Self ->
      t_Formatter ->
      (t_Formatter & Core_models.Result.t_Result Prims.unit t_Error)
    -> Type0;
  f_lower_hex_fmt:x0: v_Self -> x1: t_Formatter
    -> Prims.Pure (t_Formatter & Core_models.Result.t_Result Prims.unit t_Error)
        (f_lower_hex_fmt_pre x0 x1)
        (fun result -> f_lower_hex_fmt_post x0 x1 result)
}

/// See [`std::fmt::UpperHex`]
class t_UpperHex (v_Self: Type0) = {
  f_upper_hex_fmt_pre:v_Self -> t_Formatter -> Type0;
  f_upper_hex_fmt_post:
      v_Self ->
      t_Formatter ->
      (t_Formatter & Core_models.Result.t_Result Prims.unit t_Error)
    -> Type0;
  f_upper_hex_fmt:x0: v_Self -> x1: t_Formatter
    -> Prims.Pure (t_Formatter & Core_models.Result.t_Result Prims.unit t_Error)
        (f_upper_hex_fmt_pre x0 x1)
        (fun result -> f_upper_hex_fmt_post x0 x1 result)
}

/// See [`std::fmt::LowerExp`]
class t_LowerExp (v_Self: Type0) = {
  f_lower_exp_fmt_pre:v_Self -> t_Formatter -> Type0;
  f_lower_exp_fmt_post:
      v_Self ->
      t_Formatter ->
      (t_Formatter & Core_models.Result.t_Result Prims.unit t_Error)
    -> Type0;
  f_lower_exp_fmt:x0: v_Self -> x1: t_Formatter
    -> Prims.Pure (t_Formatter & Core_models.Result.t_Result Prims.unit t_Error)
        (f_lower_exp_fmt_pre x0 x1)
        (fun result -> f_lower_exp_fmt_post x0 x1 result)
}

/// See [`std::fmt::UpperExp`]
class t_UpperExp (v_Self: Type0) = {
  f_upper_exp_fmt_pre:v_Self -> t_Formatter -> Type0;
  f_upper_exp_fmt_post:
      v_Self ->
      t_Formatter ->
      (t_Formatter & Core_models.Result.t_Result Prims.unit t_Error)
    -> Type0;
  f_upper_exp_fmt:x0: v_Self -> x1: t_Formatter
    -> Prims.Pure (t_Formatter & Core_models.Result.t_Result Prims.unit t_Error)
        (f_upper_exp_fmt_pre x0 x1)
        (fun result -> f_upper_exp_fmt_post x0 x1 result)
}

/// See [`std::fmt::Pointer`]
class t_Pointer (v_Self: Type0) = {
  f_pointer_fmt_pre:v_Self -> t_Formatter -> Type0;
  f_pointer_fmt_post:
      v_Self ->
      t_Formatter ->
      (t_Formatter & Core_models.Result.t_Result Prims.unit t_Error)
    -> Type0;
  f_pointer_fmt:x0: v_Self -> x1: t_Formatter
    -> Prims.Pure (t_Formatter & Core_models.Result.t_Result Prims.unit t_Error)
        (f_pointer_fmt_pre x0 x1)
        (fun result -> f_pointer_fmt_post x0 x1 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Binary_for_u8:t_Binary u8

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Octal_for_u8:t_Octal u8

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_LowerHex_for_u8:t_LowerHex u8

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_UpperHex_for_u8:t_UpperHex u8

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_LowerExp_for_u8:t_LowerExp u8

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_UpperExp_for_u8:t_UpperExp u8

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Binary_for_u16:t_Binary u16

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Octal_for_u16:t_Octal u16

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_LowerHex_for_u16:t_LowerHex u16

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_UpperHex_for_u16:t_UpperHex u16

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_LowerExp_for_u16:t_LowerExp u16

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_UpperExp_for_u16:t_UpperExp u16

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Binary_for_u32:t_Binary u32

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Octal_for_u32:t_Octal u32

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_LowerHex_for_u32:t_LowerHex u32

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_UpperHex_for_u32:t_UpperHex u32

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_LowerExp_for_u32:t_LowerExp u32

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_UpperExp_for_u32:t_UpperExp u32

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Binary_for_u64:t_Binary u64

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Octal_for_u64:t_Octal u64

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_LowerHex_for_u64:t_LowerHex u64

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_UpperHex_for_u64:t_UpperHex u64

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_LowerExp_for_u64:t_LowerExp u64

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_UpperExp_for_u64:t_UpperExp u64

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Binary_for_u128:t_Binary u128

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Octal_for_u128:t_Octal u128

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_LowerHex_for_u128:t_LowerHex u128

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_UpperHex_for_u128:t_UpperHex u128

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_LowerExp_for_u128:t_LowerExp u128

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_UpperExp_for_u128:t_UpperExp u128

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Binary_for_usize:t_Binary usize

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Octal_for_usize:t_Octal usize

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_LowerHex_for_usize:t_LowerHex usize

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_UpperHex_for_usize:t_UpperHex usize

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_LowerExp_for_usize:t_LowerExp usize

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_UpperExp_for_usize:t_UpperExp usize

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Binary_for_i8:t_Binary i8

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Octal_for_i8:t_Octal i8

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_LowerHex_for_i8:t_LowerHex i8

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_UpperHex_for_i8:t_UpperHex i8

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_LowerExp_for_i8:t_LowerExp i8

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_UpperExp_for_i8:t_UpperExp i8

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Binary_for_i16:t_Binary i16

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Octal_for_i16:t_Octal i16

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_LowerHex_for_i16:t_LowerHex i16

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_UpperHex_for_i16:t_UpperHex i16

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_LowerExp_for_i16:t_LowerExp i16

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_UpperExp_for_i16:t_UpperExp i16

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Binary_for_i32:t_Binary i32

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Octal_for_i32:t_Octal i32

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_LowerHex_for_i32:t_LowerHex i32

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_UpperHex_for_i32:t_UpperHex i32

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_LowerExp_for_i32:t_LowerExp i32

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_UpperExp_for_i32:t_UpperExp i32

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Binary_for_i64:t_Binary i64

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Octal_for_i64:t_Octal i64

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_LowerHex_for_i64:t_LowerHex i64

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_UpperHex_for_i64:t_UpperHex i64

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_LowerExp_for_i64:t_LowerExp i64

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_UpperExp_for_i64:t_UpperExp i64

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Binary_for_i128:t_Binary i128

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Octal_for_i128:t_Octal i128

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_LowerHex_for_i128:t_LowerHex i128

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_UpperHex_for_i128:t_UpperHex i128

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_LowerExp_for_i128:t_LowerExp i128

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_UpperExp_for_i128:t_UpperExp i128

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Binary_for_isize:t_Binary isize

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_Octal_for_isize:t_Octal isize

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_LowerHex_for_isize:t_LowerHex isize

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_UpperHex_for_isize:t_UpperHex isize

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_LowerExp_for_isize:t_LowerExp isize

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_UpperExp_for_isize:t_UpperExp isize

/// See [`std::fmt::DebugStruct`]
type t_DebugStruct = | DebugStruct : t_DebugStruct

/// See [`std::fmt::Formatter::debug_struct`]
val impl_Formatter__debug_struct (self: t_Formatter) (label: string)
    : Prims.Pure (t_Formatter & t_DebugStruct) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::fmt::DebugStruct::finish_non_exhaustive`]
val impl_DebugStruct__finish_non_exhaustive (self: t_DebugStruct)
    : Prims.Pure (t_DebugStruct & Core_models.Result.t_Result Prims.unit t_Error)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// See [`std::fmt::DebugStruct::finish`]
val impl_DebugStruct__finish (self: t_DebugStruct)
    : Prims.Pure (t_DebugStruct & Core_models.Result.t_Result Prims.unit t_Error)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// See [`std::fmt::DebugTuple`]
type t_DebugTuple = | DebugTuple : t_DebugTuple

/// See [`std::fmt::Formatter::debug_tuple`]
val impl_Formatter__debug_tuple (self: t_Formatter) (label: string)
    : Prims.Pure (t_Formatter & t_DebugTuple) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::fmt::DebugTuple::finish_non_exhaustive`]
val impl_DebugTuple__finish_non_exhaustive (self: t_DebugTuple)
    : Prims.Pure (t_DebugTuple & Core_models.Result.t_Result Prims.unit t_Error)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// See [`std::fmt::DebugTuple::finish`]
val impl_DebugTuple__finish (self: t_DebugTuple)
    : Prims.Pure (t_DebugTuple & Core_models.Result.t_Result Prims.unit t_Error)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// See [`std::fmt::DebugList`]
type t_DebugList = | DebugList : t_DebugList

/// See [`std::fmt::Formatter::debug_list`]
val impl_Formatter__debug_list (self: t_Formatter)
    : Prims.Pure (t_Formatter & t_DebugList) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::fmt::DebugList::finish_non_exhaustive`]
val impl_DebugList__finish_non_exhaustive (self: t_DebugList)
    : Prims.Pure (t_DebugList & Core_models.Result.t_Result Prims.unit t_Error)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// See [`std::fmt::DebugList::finish`]
val impl_DebugList__finish (self: t_DebugList)
    : Prims.Pure (t_DebugList & Core_models.Result.t_Result Prims.unit t_Error)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// See [`std::fmt::DebugSet`]
type t_DebugSet = | DebugSet : t_DebugSet

/// See [`std::fmt::Formatter::debug_set`]
val impl_Formatter__debug_set (self: t_Formatter)
    : Prims.Pure (t_Formatter & t_DebugSet) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::fmt::DebugSet::finish_non_exhaustive`]
val impl_DebugSet__finish_non_exhaustive (self: t_DebugSet)
    : Prims.Pure (t_DebugSet & Core_models.Result.t_Result Prims.unit t_Error)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// See [`std::fmt::DebugSet::finish`]
val impl_DebugSet__finish (self: t_DebugSet)
    : Prims.Pure (t_DebugSet & Core_models.Result.t_Result Prims.unit t_Error)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// See [`std::fmt::DebugMap`]
/// `has_key` tracks a key waiting for its value, so that the model panics
/// exactly where real `core` asserts.
type t_DebugMap = { f_has_key:bool }

/// See [`std::fmt::Formatter::debug_map`]
val impl_Formatter__debug_map (self: t_Formatter)
    : Prims.Pure (t_Formatter & t_DebugMap) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::fmt::DebugMap::finish_non_exhaustive`]
val impl_DebugMap__finish_non_exhaustive (self: t_DebugMap)
    : Prims.Pure (t_DebugMap & Core_models.Result.t_Result Prims.unit t_Error)
      (requires self.f_has_key =. false)
      (fun _ -> Prims.l_True)

/// See [`std::fmt::DebugMap::finish`]
val impl_DebugMap__finish (self: t_DebugMap)
    : Prims.Pure (t_DebugMap & Core_models.Result.t_Result Prims.unit t_Error)
      (requires self.f_has_key =. false)
      (fun _ -> Prims.l_True)

/// See [`std::fmt::FromFn`]
type t_FromFn (v_F: Type0) = | FromFn : v_F -> t_FromFn v_F
