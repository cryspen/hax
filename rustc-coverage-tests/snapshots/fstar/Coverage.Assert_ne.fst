module Coverage.Assert_ne
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_Foo = | Foo : u32 -> t_Foo

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl': Core.Fmt.t_Debug t_Foo

unfold
let impl = impl'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': Core.Marker.t_StructuralPartialEq t_Foo

unfold
let impl_1 = impl_1'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2': Core.Cmp.t_PartialEq t_Foo t_Foo

unfold
let impl_2 = impl_2'

let main (_: Prims.unit) : Prims.unit =
  let _:Prims.unit =
    match
      Core.Hint.black_box #t_Foo (Foo (mk_u32 5) <: t_Foo),
      (if Core.Hint.black_box #bool false then Foo (mk_u32 0) <: t_Foo else Foo (mk_u32 1) <: t_Foo)
      <:
      (t_Foo & t_Foo)
    with
    | left_val, right_val -> Hax_lib.v_assert (~.(left_val =. right_val <: bool) <: bool)
  in
  () <: Prims.unit
