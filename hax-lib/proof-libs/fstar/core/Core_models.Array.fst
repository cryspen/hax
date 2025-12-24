module Core_models.Array
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

type t_TryFromSliceError = | TryFromSliceError : t_TryFromSliceError

let impl_23__map (#v_T: Type0) (v_N: usize) (#v_U: Type0) (s: t_Array v_T v_N) (f: (v_T -> v_U))
    : t_Array v_U v_N = Rust_primitives.Slice.array_map #v_T #v_U v_N s f

let impl_23__as_slice (#v_T: Type0) (v_N: usize) (s: t_Array v_T v_N) : t_Slice v_T =
  Rust_primitives.Slice.array_as_slice #v_T v_N s

let from_fn (#v_T: Type0) (v_N: usize) (f: (usize -> v_T)) : t_Array v_T v_N =
  Rust_primitives.Slice.array_from_fn #v_T v_N f
