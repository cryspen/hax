module Core.Slice
open Rust_primitives.Arrays
open Rust_primitives.Integers

let impl__len (#t: Type) (s: t_Slice t)
  : len: usize {v len == length s} = 
  sz (length s)

open Core.Slice.Iter

val impl__chunks #a (x: t_Slice a) (cs: usize): t_Chunks a

let impl__iter #t (s: t_Slice t): t_Slice t = s

val impl__chunks_exact #a (x: t_Slice a) (cs: usize):
    Pure (t_Slice (t_Slice a))
    (requires True)
    (ensures (fun r -> forall i. i < length x ==> length x ==  v cs))

open Core.Ops.Index

instance impl__index t n: t_Index (t_Slice t) (int_t n)
  = { f_Output = t;
      f_index_pre = (fun (s: t_Slice t) (i: int_t n) -> v i >= 0 && v i < length s);
      f_index_post = (fun _ _ _ -> true);
      f_index = (fun s i -> index s (v i));
    }

let impl__copy_from_slice #t (x: t_Slice t) (y:t_Slice t) : t_Slice t = y
let impl__clone_from_slice #t (x: t_Slice t) (y:t_Slice t) : t_Slice t = y

val impl__split_at #t (s: t_Slice t) (mid: usize): Pure (t_Slice t * t_Slice t)
    (requires (v mid <= length s))
    (ensures (fun (x,y) -> length x == v mid /\ length y == length s - v mid /\
                        x == slice s 0 (v mid) /\ y == slice s (v mid) (length s) /\
                        s == concat x y))

let impl__is_empty (s: t_Slice 'a): bool = length s = 0

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
