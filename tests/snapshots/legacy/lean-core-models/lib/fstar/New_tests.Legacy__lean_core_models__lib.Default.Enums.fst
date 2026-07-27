module New_tests.Legacy__lean_core_models__lib.Default.Enums
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_E (v_T: Type0) =
  | E_C1 : u32 -> t_E v_T
  | E_C2 : v_T -> t_E v_T

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Default.t_Default v_T)
    : Core_models.Default.t_Default (t_E v_T) =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: t_E v_T) -> true);
    f_default
    =
    fun (_: Prims.unit) ->
      E_C2 (Core_models.Default.f_default #v_T #FStar.Tactics.Typeclasses.solve ()) <: t_E v_T
  }
