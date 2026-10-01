module New_tests.Legacy__reconstruct_asserts_else__lib
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// Value in the else branch.
let checked_incr (c: bool) (x: u32) : u32 =
  if c
  then
    Rust_primitives.Hax.never_to_any (Core_models.Panicking.panic "explicit panic"
        <:
        Rust_primitives.Hax.t_Never)
  else x +! mk_u32 1

/// Nested panic-elses.
let nested (c d: bool) (x: u32) : u32 =
  if c
  then
    Rust_primitives.Hax.never_to_any (Core_models.Panicking.panic "explicit panic"
        <:
        Rust_primitives.Hax.t_Never)
  else
    if d
    then
      Rust_primitives.Hax.never_to_any (Core_models.Panicking.panic "explicit panic"
          <:
          Rust_primitives.Hax.t_Never)
    else x

/// No else.
let bare (c: bool) : Prims.unit = Hax_lib.v_assert (~.c <: bool)
