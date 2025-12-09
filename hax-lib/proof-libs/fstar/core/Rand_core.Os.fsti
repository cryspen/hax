module Rand_core.Os
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Rand_core in
  ()

type t_OsRng = | OsRng : t_OsRng

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl:Rand_core.t_RngCore t_OsRng

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_1:Rand_core.t_CryptoRng t_OsRng
