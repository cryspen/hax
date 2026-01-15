module Tests.Legacy__cli__include_flag__src__lib
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_Foo = | Foo : t_Foo

class t_Trait (v_Self: Type0) = { __marker_trait_t_Trait:Prims.unit }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_Trait t_Foo = { __marker_trait_t_Trait = () }

/// Indirect dependencies
let main_a_a (_: Prims.unit) : Prims.unit = ()

let main_b_a (_: Prims.unit) : Prims.unit = ()

let main_c_a (_: Prims.unit) : Prims.unit = ()

let main_a_b (_: Prims.unit) : Prims.unit = ()

let main_b_b (_: Prims.unit) : Prims.unit = ()

let main_c_b (_: Prims.unit) : Prims.unit = ()

let main_a_c (_: Prims.unit) : Prims.unit = ()

/// Direct dependencies
let main_a (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Trait v_T) (x: v_T)
    : Prims.unit =
  let _:Prims.unit = main_a_a () in
  let _:Prims.unit = main_a_b () in
  let _:Prims.unit = main_a_c () in
  ()

let main_b_c (_: Prims.unit) : Prims.unit = ()

let main_b (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = main_b_a () in
  let _:Prims.unit = main_b_b () in
  let _:Prims.unit = main_b_c () in
  ()

let main_c_c (_: Prims.unit) : Prims.unit = ()

let main_c (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = main_c_a () in
  let _:Prims.unit = main_c_b () in
  let _:Prims.unit = main_c_c () in
  ()

/// Entrypoint
let main (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = main_a #t_Foo (Foo <: t_Foo) in
  let _:Prims.unit = main_b () in
  let _:Prims.unit = main_c () in
  ()
