module Tests.Legacy__traits.Implicit_dependencies_issue_667_.Use_type
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Tests.Legacy__traits.Implicit_dependencies_issue_667_.Impl_type in
  let open Tests.Legacy__traits.Implicit_dependencies_issue_667_.Trait_definition in
  ()

let some_function (x: Tests.Legacy__traits.Implicit_dependencies_issue_667_.Define_type.t_MyType)
    : Prims.unit =
  Tests.Legacy__traits.Implicit_dependencies_issue_667_.Trait_definition.f_my_method #Tests.Legacy__traits.Implicit_dependencies_issue_667_.Define_type.t_MyType
    #FStar.Tactics.Typeclasses.solve
    x
