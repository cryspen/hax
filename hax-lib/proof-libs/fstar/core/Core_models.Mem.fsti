module Core_models.Mem
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

val forget (#v_T: Type0) (t: v_T) : Prims.Pure Prims.unit Prims.l_True (fun _ -> Prims.l_True)

val forget__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val forget_unsized (#v_T: Type0) (t: v_T)
    : Prims.Pure Prims.unit Prims.l_True (fun _ -> Prims.l_True)

val forget_unsized__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val size_of: #v_T: Type0 -> Prims.unit -> Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

val size_of__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val size_of_val (#v_T: Type0) (v_val: v_T) : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

val size_of_val__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val min_align_of: #v_T: Type0 -> Prims.unit -> Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

val min_align_of__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val min_align_of_val (#v_T: Type0) (v_val: v_T)
    : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

val min_align_of_val__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val align_of: #v_T: Type0 -> Prims.unit -> Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

val align_of__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val align_of_val (#v_T: Type0) (v_val: v_T) : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

val align_of_val__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val align_of_val_raw (#v_T: Type0) (v_val: v_T)
    : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

val align_of_val_raw__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val needs_drop: #v_T: Type0 -> Prims.unit -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

val needs_drop__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val uninitialized: #v_T: Type0 -> Prims.unit -> Prims.Pure v_T Prims.l_True (fun _ -> Prims.l_True)

val uninitialized__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val swap (#v_T: Type0) (x y: v_T) : Prims.Pure (v_T & v_T) Prims.l_True (fun _ -> Prims.l_True)

val swap__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val replace (#v_T: Type0) (dest src: v_T)
    : Prims.Pure (v_T & v_T) Prims.l_True (fun _ -> Prims.l_True)

val replace__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val drop (#v_T: Type0) (e_x: v_T) : Prims.Pure Prims.unit Prims.l_True (fun _ -> Prims.l_True)

val copy (#v_T: Type0) {| i0: Core_models.Marker.t_Copy v_T |} (x: v_T)
    : Prims.Pure v_T Prims.l_True (fun _ -> Prims.l_True)

val take (#v_T: Type0) (x: v_T) : Prims.Pure (v_T & v_T) Prims.l_True (fun _ -> Prims.l_True)

val take__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val transmute_copy (#v_Src #v_Dst: Type0) (src: v_Src)
    : Prims.Pure v_Dst Prims.l_True (fun _ -> Prims.l_True)

val transmute_copy__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val variant_count: #v_T: Type0 -> Prims.unit
  -> Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

val variant_count__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val zeroed: #v_T: Type0 -> Prims.unit -> Prims.Pure v_T Prims.l_True (fun _ -> Prims.l_True)

val zeroed__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val transmute (#v_Src #v_Dst: Type0) (src: v_Src)
    : Prims.Pure v_Dst Prims.l_True (fun _ -> Prims.l_True)

val transmute__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)
