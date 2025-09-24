module Alloc.Collections.Vec_deque
open Rust_primitives

unfold type t_VecDeque t (_: unit) = t_Slice t

val impl_5__push_back #t #a (v: t_VecDeque t a) (x: t): t_VecDeque t a

let impl_5__len #t #a (v: t_VecDeque t a): usize = sz (Seq.length v)

let impl_5__pop_front #t #a (v: t_VecDeque t a): t_VecDeque t a & Core_models.Option.t_Option t = 
  match Seq.seq_to_list v with 
  | h::tail -> Seq.seq_of_list tail,  Core_models.Option.Option_Some h 
  | [] -> v, Core_models.Option.Option_None


[@FStar.Tactics.Typeclasses.tcinstance]
val from_vec_deque_array t a n: Core_models.Convert.t_From (Alloc.Collections.Vec_deque.t_VecDeque t a)
        (Rust_primitives.Arrays.t_Array t
            (Rust_primitives.Integers.mk_usize n))


val index_vec_deque t a: Core_models.Ops.Index.t_Index (Alloc.Collections.Vec_deque.t_VecDeque t a)
        Rust_primitives.Integers.usize
