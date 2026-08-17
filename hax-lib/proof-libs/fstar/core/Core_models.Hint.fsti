module Core_models.Hint
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::hint::black_box`]
val black_box (#v_T: Type0) (dummy: v_T)
    : Prims.Pure v_T
      Prims.l_True
      (ensures
        fun res ->
          let res:v_T = res in
          res == dummy)

/// See [`std::hint::must_use`]
val must_use (#v_T: Type0) (value: v_T)
    : Prims.Pure v_T
      Prims.l_True
      (ensures
        fun res ->
          let res:v_T = res in
          res == value)

/// See [`std::hint::likely`]
val likely (b: bool)
    : Prims.Pure bool
      Prims.l_True
      (ensures
        fun res ->
          let res:bool = res in
          res == b)

/// See [`std::hint::unlikely`]
val unlikely (b: bool)
    : Prims.Pure bool
      Prims.l_True
      (ensures
        fun res ->
          let res:bool = res in
          res == b)

/// See [`std::hint::select_unpredictable`]
val select_unpredictable (#v_T: Type0) (condition: bool) (true_val false_val: v_T)
    : Prims.Pure v_T
      Prims.l_True
      (ensures
        fun res ->
          let res:v_T = res in
          res == (if condition then true_val else false_val))

/// See [`std::hint::spin_loop`]
val spin_loop: Prims.unit -> Prims.Pure Prims.unit Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::hint::cold_path`]
val cold_path: Prims.unit -> Prims.Pure Prims.unit Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::hint::unreachable_unchecked`]. UB in Rust; modeled as an
/// unreachable panic, with `requires(false)` so callers must prove it is never
/// hit (same treatment as [`crate::intrinsics::unreachable`]).
val unreachable_unchecked: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never (requires false) (fun _ -> Prims.l_True)

/// See [`std::hint::assert_unchecked`]. UB in Rust when `cond` is false, so the
/// `requires` rules that case out and the model panics on it.
val assert_unchecked (cond: bool) : Prims.Pure Prims.unit (requires cond) (fun _ -> Prims.l_True)

/// See [`std::hint::Locality`]
type t_Locality =
  | Locality_L3 : t_Locality
  | Locality_L2 : t_Locality
  | Locality_L1 : t_Locality

val t_Locality_cast_to_repr (x: t_Locality) : Prims.Pure isize Prims.l_True (fun _ -> Prims.l_True)
