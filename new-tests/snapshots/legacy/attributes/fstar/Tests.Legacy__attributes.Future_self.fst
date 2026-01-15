module Tests.Legacy__attributes.Future_self
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_Dummy = | Dummy : t_Dummy

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': Core_models.Marker.t_StructuralPartialEq t_Dummy

unfold
let impl_1 = impl_1'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2': Core_models.Cmp.t_PartialEq t_Dummy t_Dummy

unfold
let impl_2 = impl_2'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl': Core_models.Cmp.t_Eq t_Dummy

unfold
let impl = impl'

let impl_Dummy__f (self: t_Dummy)
    : Prims.Pure t_Dummy
      Prims.l_True
      (ensures
        fun self_e_future ->
          let self_e_future:t_Dummy = self_e_future in
          self_e_future =. self) = self
