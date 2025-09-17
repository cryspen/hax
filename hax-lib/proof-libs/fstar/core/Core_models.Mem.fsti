module Core_models.Mem
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val replace (#v_T: Type0) (dest src: v_T)
    : Prims.Pure (v_T & v_T) Prims.l_True (fun _ -> Prims.l_True)

val replace__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)
