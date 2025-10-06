module Tests.Legacy__naming.Functions_defined_in_trait_impls
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_A = | A : t_A

let f_eq__impl__panic_cold_explicit (_: Prims.unit) : Rust_primitives.Hax.t_Never =
  Core.Panicking.panic_explicit ()

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core.Cmp.t_PartialEq t_A t_A =
  {
    f_eq_pre = (fun (self: t_A) (other: t_A) -> true);
    f_eq_post = (fun (self: t_A) (other: t_A) (out: bool) -> true);
    f_eq
    =
    fun (self: t_A) (other: t_A) ->
      Rust_primitives.Hax.never_to_any (f_eq__impl__panic_cold_explicit ()
          <:
          Rust_primitives.Hax.t_Never)
  }

type t_B = | B : t_B

let f_eq__impl_1__panic_cold_explicit (_: Prims.unit) : Rust_primitives.Hax.t_Never =
  Core.Panicking.panic_explicit ()

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core.Cmp.t_PartialEq t_B t_B =
  {
    f_eq_pre = (fun (self: t_B) (other: t_B) -> true);
    f_eq_post = (fun (self: t_B) (other: t_B) (out: bool) -> true);
    f_eq
    =
    fun (self: t_B) (other: t_B) ->
      Rust_primitives.Hax.never_to_any (f_eq__impl_1__panic_cold_explicit ()
          <:
          Rust_primitives.Hax.t_Never)
  }
