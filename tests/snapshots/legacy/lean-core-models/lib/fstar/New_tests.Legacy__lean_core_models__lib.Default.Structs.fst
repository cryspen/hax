module New_tests.Legacy__lean_core_models__lib.Default.Structs
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_S = { f_f1:usize }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core_models.Default.t_Default t_S =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: t_S) -> true);
    f_default = fun (_: Prims.unit) -> { f_f1 = mk_usize 0 } <: t_S
  }

let test (_: Prims.unit) : t_S =
  Core_models.Default.f_default #t_S #FStar.Tactics.Typeclasses.solve ()
