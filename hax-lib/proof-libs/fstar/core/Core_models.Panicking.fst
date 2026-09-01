module Core_models.Panicking
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
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

/// `core::panicking::panic_nounwind`. The model does not distinguish unwinding
/// from aborting, so this is `panic` by another name.
assume
val panic_nounwind': e_expr: string
  -> Prims.Pure Rust_primitives.Hax.t_Never (requires false) (fun _ -> Prims.l_True)

unfold
let panic_nounwind = panic_nounwind'

/// `core::panicking::panic_nounwind_nobacktrace`. Backtraces are not modeled;
/// the `&str` deviation is the same as for `panic_nounwind`.
assume
val panic_nounwind_nobacktrace': e_expr: string
  -> Prims.Pure Rust_primitives.Hax.t_Never (requires false) (fun _ -> Prims.l_True)

unfold
let panic_nounwind_nobacktrace = panic_nounwind_nobacktrace'

/// `core::panicking::panic_nounwind_fmt`
assume
val panic_nounwind_fmt': e_fmt: Core_models.Fmt.t_Arguments -> e_force_no_backtrace: bool
  -> Prims.Pure Rust_primitives.Hax.t_Never (requires false) (fun _ -> Prims.l_True)

unfold
let panic_nounwind_fmt = panic_nounwind_fmt'

/// `core::panicking::const_panic_fmt` — what const-eval calls in place of
/// `panic_fmt`.
assume
val const_panic_fmt': e_fmt: Core_models.Fmt.t_Arguments
  -> Prims.Pure Rust_primitives.Hax.t_Never (requires false) (fun _ -> Prims.l_True)

unfold
let const_panic_fmt = const_panic_fmt'

/// `core::panicking::panic_str_2015`, the 2015-edition `panic!(var)` entry point.
assume
val panic_str_2015_': e_expr: string
  -> Prims.Pure Rust_primitives.Hax.t_Never (requires false) (fun _ -> Prims.l_True)

unfold
let panic_str_2015_ = panic_str_2015_'

/// `core::panicking::panic_display`
assume
val panic_display': #v_T: Type0 -> {| i0: Core_models.Fmt.t_Display v_T |} -> e_x: v_T
  -> Prims.Pure Rust_primitives.Hax.t_Never (requires false) (fun _ -> Prims.l_True)

unfold
let panic_display
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Fmt.t_Display v_T)
     = panic_display' #v_T #i0

/// `core::panicking::unreachable_display`
assume
val unreachable_display': #v_T: Type0 -> {| i0: Core_models.Fmt.t_Display v_T |} -> e_x: v_T
  -> Prims.Pure Rust_primitives.Hax.t_Never (requires false) (fun _ -> Prims.l_True)

unfold
let unreachable_display
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Fmt.t_Display v_T)
     = unreachable_display' #v_T #i0
