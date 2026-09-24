module Rand.Rng
open Rust_primitives

/// See `rand::Rng`: its methods are provided ones, so the class only has its
/// `RngCore` supertrait.
class t_Rng (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:Rand_core.t_RngCore v_Self
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_Rng v_Self|} -> i._super_i0

/// `rand`'s blanket `impl<R: RngCore + ?Sized> Rng for R`.
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_R: Type0) {| i0: Rand_core.t_RngCore v_R |} : t_Rng v_R = { _super_i0 = i0 }
