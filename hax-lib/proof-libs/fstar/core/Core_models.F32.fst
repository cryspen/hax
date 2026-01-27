module Core_models.F32
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

assume
val impl_f32__abs': x: float -> float

unfold
let impl_f32__abs = impl_f32__abs'
