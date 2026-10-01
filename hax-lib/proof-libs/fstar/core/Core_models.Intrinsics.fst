module Core_models.Intrinsics
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`core::intrinsics::unreachable`]. UB in Rust; modeled as an unreachable
/// panic, with `requires(false)` so callers must prove it is never hit.
assume
val unreachable': Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never (requires false) (fun _ -> Prims.l_True)

unfold
let unreachable = unreachable'
