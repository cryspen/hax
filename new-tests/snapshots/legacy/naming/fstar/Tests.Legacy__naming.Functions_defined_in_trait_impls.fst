module Tests.Legacy__naming.Functions_defined_in_trait_impls
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_A = | A : t_A

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core_models.Cmp.t_PartialEq t_A t_A =
  {
    f_eq_pre = (fun (self: t_A) (other: t_A) -> true);
    f_eq_post = (fun (self: t_A) (other: t_A) (out: bool) -> true);
    f_eq
    =
    fun (self: t_A) (other: t_A) ->
      Rust_primitives.Hax.never_to_any (Core_models.Panicking.panic "explicit panic"
          <:
          Rust_primitives.Hax.t_Never)
  }

type t_B = | B : t_B

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core_models.Cmp.t_PartialEq t_B t_B =
  {
    f_eq_pre = (fun (self: t_B) (other: t_B) -> true);
    f_eq_post = (fun (self: t_B) (other: t_B) (out: bool) -> true);
    f_eq
    =
    fun (self: t_B) (other: t_B) ->
      Rust_primitives.Hax.never_to_any (Core_models.Panicking.panic "explicit panic"
          <:
          Rust_primitives.Hax.t_Never)
  }
