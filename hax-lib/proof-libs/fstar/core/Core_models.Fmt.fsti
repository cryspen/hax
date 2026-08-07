module Core_models.Fmt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::fmt::Error`]
type t_Error = | Error : t_Error

/// See [`std::fmt::Formatter`]
type t_Formatter = | Formatter : t_Formatter

val impl_Formatter__write_str (self: t_Formatter) (data: string)
    : Prims.Pure (t_Formatter & Core_models.Result.t_Result Prims.unit t_Error)
      Prims.l_True
      (fun _ -> Prims.l_True)

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

/// See [`std::fmt::Arguments`]
type t_Arguments = | Arguments : Prims.unit -> t_Arguments

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
