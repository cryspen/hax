module Core_models.Panicking
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

assume
val panic_explicit': Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never (requires false) (fun _ -> Prims.l_True)

unfold
let panic_explicit = panic_explicit'

assume
val panic_explicit__panic_cold_explicit': Prims.unit -> Rust_primitives.Hax.t_Never

unfold
let panic_explicit__panic_cold_explicit = panic_explicit__panic_cold_explicit'

assume
val panic': e_msg: string
  -> Prims.Pure Rust_primitives.Hax.t_Never (requires false) (fun _ -> Prims.l_True)

unfold
let panic = panic'

assume
val panic__panic_cold_explicit': Prims.unit -> Rust_primitives.Hax.t_Never

unfold
let panic__panic_cold_explicit = panic__panic_cold_explicit'

assume
val panic_fmt': e_fmt: Core_models.Fmt.Rt.t_Argument
  -> Prims.Pure Rust_primitives.Hax.t_Never (requires false) (fun _ -> Prims.l_True)

unfold
let panic_fmt = panic_fmt'

assume
val panic_fmt__panic_cold_explicit': Prims.unit -> Rust_primitives.Hax.t_Never

unfold
let panic_fmt__panic_cold_explicit = panic_fmt__panic_cold_explicit'
