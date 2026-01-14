module Core_models.Mem
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul

open Rust_primitives.Integers

assume
val forget': #v_T: Type0 -> t: v_T -> Prims.unit

unfold
let forget (#v_T: Type0) = forget' #v_T

assume
val forget_unsized': #v_T: Type0 -> t: v_T -> Prims.unit

unfold
let forget_unsized (#v_T: Type0) = forget_unsized' #v_T

assume
val size_of': #v_T: Type0 -> Prims.unit -> usize

unfold
let size_of (#v_T: Type0) = size_of' #v_T

assume
val size_of_val': #v_T: Type0 -> v_val: v_T -> usize

unfold
let size_of_val (#v_T: Type0) = size_of_val' #v_T

assume
val min_align_of': #v_T: Type0 -> Prims.unit -> usize

unfold
let min_align_of (#v_T: Type0) = min_align_of' #v_T

assume
val min_align_of_val': #v_T: Type0 -> v_val: v_T -> usize

unfold
let min_align_of_val (#v_T: Type0) = min_align_of_val' #v_T

assume
val align_of': #v_T: Type0 -> Prims.unit -> usize

unfold
let align_of (#v_T: Type0) = align_of' #v_T

assume
val align_of_val': #v_T: Type0 -> v_val: v_T -> usize

unfold
let align_of_val (#v_T: Type0) = align_of_val' #v_T

assume
val align_of_val_raw': #v_T: Type0 -> v_val: v_T -> usize

unfold
let align_of_val_raw (#v_T: Type0) = align_of_val_raw' #v_T

assume
val needs_drop': #v_T: Type0 -> Prims.unit -> bool

unfold
let needs_drop (#v_T: Type0) = needs_drop' #v_T

assume
val uninitialized': #v_T: Type0 -> Prims.unit -> v_T

unfold
let uninitialized (#v_T: Type0) = uninitialized' #v_T

assume
val swap': #v_T: Type0 -> x: v_T -> y: v_T -> (v_T & v_T)

unfold
let swap (#v_T: Type0) = swap' #v_T

assume
val replace': #v_T: Type0 -> dest: v_T -> src: v_T -> (v_T & v_T)

unfold
let replace (#v_T: Type0) = replace' #v_T

assume
val drop': #v_T: Type0 -> e_x: v_T -> Prims.unit

unfold
let drop (#v_T: Type0) = drop' #v_T

let copy
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Marker.t_Copy v_T)
      (x: v_T)
    : v_T = x

assume
val take': #v_T: Type0 -> x: v_T -> (v_T & v_T)

unfold
let take (#v_T: Type0) = take' #v_T

assume
val transmute_copy': #v_Src: Type0 -> #v_Dst: Type0 -> src: v_Src -> v_Dst

unfold
let transmute_copy (#v_Src #v_Dst: Type0) = transmute_copy' #v_Src #v_Dst

assume
val variant_count': #v_T: Type0 -> Prims.unit -> usize

unfold
let variant_count (#v_T: Type0) = variant_count' #v_T

assume
val zeroed': #v_T: Type0 -> Prims.unit -> v_T

unfold
let zeroed (#v_T: Type0) = zeroed' #v_T
