module Tests.Legacy__never_type
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_False =

let t_False_cast_to_repr (x: t_False) : Rust_primitives.Hax.t_Never = match x <: t_False with

let never (h: t_False) : Rust_primitives.Hax.t_Never = match h <: t_False with

let test__panic_cold_explicit (_: Prims.unit) : Rust_primitives.Hax.t_Never =
  Core.Panicking.panic_explicit ()

let test (b: bool) : u8 =
  let _:Prims.unit =
    if b
    then
      Rust_primitives.Hax.never_to_any (test__panic_cold_explicit () <: Rust_primitives.Hax.t_Never)
  in
  mk_u8 3

let any__panic_cold_explicit (_: Prims.unit) : Rust_primitives.Hax.t_Never =
  Core.Panicking.panic_explicit ()

let any (#v_T: Type0) (_: Prims.unit) : v_T =
  Rust_primitives.Hax.never_to_any (any__panic_cold_explicit () <: Rust_primitives.Hax.t_Never)
