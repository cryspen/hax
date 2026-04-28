module Alloc.Vec.Into_iter
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

type t_IntoIter (v_T: Type0) (v_A: Type0) =
  | IntoIter : Rust_primitives.Sequence.t_Seq v_T -> Core_models.Marker.t_PhantomData v_A
    -> t_IntoIter v_T v_A
