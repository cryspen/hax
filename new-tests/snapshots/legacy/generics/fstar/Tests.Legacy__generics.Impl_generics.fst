module Tests.Legacy__generics.Impl_generics
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_Test = | Test : t_Test

let impl_Test__set_ciphersuites
      (#v_S #iimpl_995885649_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Convert.t_AsRef v_S string)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Iter.Traits.Collect.t_IntoIterator iimpl_995885649_)
      (#_: unit{i1.Core_models.Iter.Traits.Collect.f_Item == v_S})
      (self: t_Test)
      (ciphers: iimpl_995885649_)
    : Core_models.Result.t_Result Prims.unit Prims.unit =
  Core_models.Result.Result_Ok (() <: Prims.unit)
  <:
  Core_models.Result.t_Result Prims.unit Prims.unit

let impl_Test__set_alpn_protocols
      (#v_S #iimpl_995885649_: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Convert.t_AsRef v_S string)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Iter.Traits.Collect.t_IntoIterator iimpl_995885649_)
      (#_: unit{i1.Core_models.Iter.Traits.Collect.f_Item == v_S})
      (self: t_Test)
      (e_protocols: iimpl_995885649_)
    : Core_models.Result.t_Result Prims.unit Prims.unit =
  Core_models.Result.Result_Ok (() <: Prims.unit)
  <:
  Core_models.Result.t_Result Prims.unit Prims.unit
