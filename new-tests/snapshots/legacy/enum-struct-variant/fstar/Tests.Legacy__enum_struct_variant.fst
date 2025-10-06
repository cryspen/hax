module Tests.Legacy__enum_struct_variant
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_Money = { f_value:u64 }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl': Core.Fmt.t_Debug t_Money

unfold
let impl = impl'

type t_EnumWithStructVariant =
  | EnumWithStructVariant_Funds { f_balance:t_Money }: t_EnumWithStructVariant

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': Core.Fmt.t_Debug t_EnumWithStructVariant

unfold
let impl_1 = impl_1'
