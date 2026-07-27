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
