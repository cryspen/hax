module Tests.Legacy__unsafe
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_Impossible =

let t_Impossible_cast_to_repr (x: t_Impossible) : Rust_primitives.Hax.t_Never =
  match x <: t_Impossible with

/// @fail(extraction): ssprove(HAX0008), coq(HAX0008)
let impossible (_: Prims.unit) : Prims.Pure t_Impossible (requires false) (fun _ -> Prims.l_True) =
  Rust_primitives.Hax.never_to_any (Core_models.Hint.unreachable_unchecked ()
      <:
      Rust_primitives.Hax.t_Never)

/// @fail(extraction): ssprove(HAX0008), coq(HAX0008)
let get_unchecked_example (slice: t_Slice u8)
    : Prims.Pure u8
      (requires (Core_models.Slice.impl__len #u8 slice <: usize) >. mk_usize 10)
      (fun _ -> Prims.l_True) = Core_models.Slice.impl__get_unchecked #u8 #usize slice (mk_usize 6)
