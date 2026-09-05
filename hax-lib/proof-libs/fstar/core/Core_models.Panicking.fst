module Core_models.Panicking
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Rust_primitives

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

/// `core::panicking::AssertKind` — which of `assert_eq!` / `assert_ne!` /
/// `assert_matches!` failed. Carried by the `assert_failed` shims; the model
/// has no use for it beyond giving a client's mention of it a name.
type t_AssertKind =
  | AssertKind_Eq : t_AssertKind
  | AssertKind_Ne : t_AssertKind
  | AssertKind_Match : t_AssertKind

let t_AssertKind_cast_to_repr (x: t_AssertKind) : isize =
  match x <: t_AssertKind with
  | AssertKind_Eq  -> mk_isize 0
  | AssertKind_Ne  -> mk_isize 1
  | AssertKind_Match  -> mk_isize 2
