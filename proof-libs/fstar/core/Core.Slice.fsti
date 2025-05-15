module Core.Slice
open Rust_primitives.Arrays
open Rust_primitives.Integers

let impl__len (#t: Type) (s: t_Slice t)
  : len: usize {len == length s} = 
  length s

open Core.Slice.Iter

val impl__chunks #a (x: t_Slice a) (cs: usize): t_Chunks a

let impl__iter #t (s: t_Slice t): t_Slice t = s

val impl__chunks_exact #a (x: t_Slice a) (cs: usize):
    Pure (t_Slice (t_Slice a))
    (requires True)
    (ensures (fun r -> forall i. i < v (length x) ==> length x ==  cs))

open Core.Ops.Index

instance impl__index t n: t_Index (t_Slice t) (int_t n)
  = { f_Output = t;
      f_index_pre = (fun (s: t_Slice t) (i: int_t n) -> v i >= 0 && v i < v (length s));
      f_index_post = (fun _ _ _ -> true);
      f_index = (fun s i -> index s (sz (v i)));
    }

let impl__copy_from_slice #t (x: t_Slice t) (y:t_Slice t) : t_Slice t = y
let impl__clone_from_slice #t (x: t_Slice t) (y:t_Slice t) : t_Slice t = y

val impl__split_at #t (s: t_Slice t) (mid: usize): Pure (t_Slice t * t_Slice t)
    (requires (mid <=. length s))
    (ensures (fun (x,y) -> length x == mid /\ length y == length s -. mid /\
                        x == slice s (sz 0) mid /\ y == slice s mid (length s) /\
                        s == concat x y))

let impl__is_empty (s: t_Slice 'a): bool = length s = sz 0

let impl__contains (#t: eqtype) (s: t_Slice t) (v: t) =
  mem v s 

val impl__copy_within
      (#v_T #v_R: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve
            ()]
          i3:
          Core.Marker.t_Copy v_T)
      (v: t_Slice v_T)
      (src: v_R)
      (dest: usize)
    : t_Slice v_T

val impl__binary_search #t (s: t_Slice t) (v: t): Core.Result.t_Result usize usize
