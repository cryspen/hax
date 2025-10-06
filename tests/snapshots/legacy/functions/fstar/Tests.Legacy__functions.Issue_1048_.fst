module Tests.Legacy__functions.Issue_1048_
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_CallableViaDeref = | CallableViaDeref : t_CallableViaDeref

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core.Ops.Deref.t_Deref t_CallableViaDeref =
  {
    f_Target = Prims.unit -> bool;
    f_deref_pre = (fun (self: t_CallableViaDeref) -> true);
    f_deref_post = (fun (self: t_CallableViaDeref) (out: (Prims.unit -> bool)) -> true);
    f_deref
    =
    fun (self: t_CallableViaDeref) ->
      fun temp_0_ ->
        let _:Prims.unit = temp_0_ in
        true
  }

/// @fail(extraction): coq(HAX0002)
let call_via_deref (_: Prims.unit) : bool =
  Core.Ops.Deref.f_deref #t_CallableViaDeref
    #FStar.Tactics.Typeclasses.solve
    (CallableViaDeref <: t_CallableViaDeref)
    ()
