module Core_models.Fmt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul

type t_Error = | Error : t_Error

type t_Formatter = | Formatter : t_Formatter

class t_Display (v_Self: Type0) = {
  f_fmt_pre:v_Self -> t_Formatter -> Type0;
  f_fmt_post:v_Self -> t_Formatter -> (t_Formatter & Core_models.Result.t_Result Prims.unit t_Error)
    -> Type0;
  f_fmt:x0: v_Self -> x1: t_Formatter
    -> Prims.Pure (t_Formatter & Core_models.Result.t_Result Prims.unit t_Error)
        (f_fmt_pre x0 x1)
        (fun result -> f_fmt_post x0 x1 result)
}

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

type t_Arguments = | Arguments : t_Arguments

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl (#v_T: Type0) : t_Debug v_T
