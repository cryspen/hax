module Tests.Legacy__never_type
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_False =

let t_False_cast_to_repr (x: t_False) : Rust_primitives.Hax.t_Never = match x <: t_False with

let never (h: t_False) : Rust_primitives.Hax.t_Never = match h <: t_False with

let test (b: bool) : u8 =
  let _:Prims.unit =
    if b
    then
      Rust_primitives.Hax.never_to_any (Core_models.Panicking.panic "explicit panic"
          <:
          Rust_primitives.Hax.t_Never)
  in
  mk_u8 3

let any (#v_T: Type0) (_: Prims.unit) : v_T =
  Rust_primitives.Hax.never_to_any (Core_models.Panicking.panic "explicit panic"
      <:
      Rust_primitives.Hax.t_Never)
