module Tests.Legacy__generics.Impl_generics
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_Test = | Test : t_Test

let impl_Test__set_ciphersuites
      (#v_S #iimpl_995885649_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core.Convert.t_AsRef v_S string)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core.Iter.Traits.Collect.t_IntoIterator iimpl_995885649_)
      (self: t_Test)
      (ciphers: iimpl_995885649_)
    : Core.Result.t_Result Prims.unit Prims.unit =
  Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit Prims.unit

let impl_Test__set_alpn_protocols
      (#v_S #iimpl_995885649_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core.Convert.t_AsRef v_S string)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core.Iter.Traits.Collect.t_IntoIterator iimpl_995885649_)
      (self: t_Test)
      (e_protocols: iimpl_995885649_)
    : Core.Result.t_Result Prims.unit Prims.unit =
  Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit Prims.unit
