module Core_models.Panicking
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul

assume
val panic_explicit': Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never (requires false) (fun _ -> Prims.l_True)

unfold
let panic_explicit = panic_explicit'

assume
val panic': e_msg: string
  -> Prims.Pure Rust_primitives.Hax.t_Never (requires false) (fun _ -> Prims.l_True)

unfold
let panic = panic'

assume
val panic_fmt': e_fmt: Core_models.Fmt.t_Arguments
  -> Prims.Pure Rust_primitives.Hax.t_Never (requires false) (fun _ -> Prims.l_True)

unfold
let panic_fmt = panic_fmt'
