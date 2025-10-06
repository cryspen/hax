module Tests.Legacy__traits.Implement_arithmetic_trait
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_Wrapped = | Wrapped : i32 -> t_Wrapped

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core.Ops.Arith.t_Add t_Wrapped t_Wrapped =
  {
    f_Output = t_Wrapped;
    f_add_pre = (fun (self: t_Wrapped) (rhs: t_Wrapped) -> true);
    f_add_post = (fun (self: t_Wrapped) (rhs: t_Wrapped) (out: t_Wrapped) -> true);
    f_add = fun (self: t_Wrapped) (rhs: t_Wrapped) -> Wrapped (self._0 +! rhs._0) <: t_Wrapped
  }

let test (x y: t_Wrapped) : t_Wrapped =
  Core.Ops.Arith.f_add #t_Wrapped #t_Wrapped #FStar.Tactics.Typeclasses.solve x y
