module Tests.Legacy__traits.Implicit_dependencies_issue_667_.Impl_type
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Tests.Legacy__traits.Implicit_dependencies_issue_667_.Trait_definition.t_MyTrait
Tests.Legacy__traits.Implicit_dependencies_issue_667_.Define_type.t_MyType =
  {
    f_my_method_pre
    =
    (fun (self: Tests.Legacy__traits.Implicit_dependencies_issue_667_.Define_type.t_MyType) -> true);
    f_my_method_post
    =
    (fun
        (self: Tests.Legacy__traits.Implicit_dependencies_issue_667_.Define_type.t_MyType)
        (out: Prims.unit)
        ->
        true);
    f_my_method
    =
    fun (self: Tests.Legacy__traits.Implicit_dependencies_issue_667_.Define_type.t_MyType) -> ()
  }
