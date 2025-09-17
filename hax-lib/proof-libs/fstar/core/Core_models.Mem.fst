module Core_models.Mem
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul

assume
val forget__panic_cold_explicit': Prims.unit -> Rust_primitives.Hax.t_Never

unfold
let forget__panic_cold_explicit = forget__panic_cold_explicit'

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
val forget_unsized__panic_cold_explicit': Prims.unit -> Rust_primitives.Hax.t_Never

unfold
let forget_unsized__panic_cold_explicit = forget_unsized__panic_cold_explicit'

assume
val size_of': #v_T: Type0 -> Prims.unit -> usize

unfold
let size_of (#v_T: Type0) = size_of' #v_T

assume
val size_of__panic_cold_explicit': Prims.unit -> Rust_primitives.Hax.t_Never

unfold
let size_of__panic_cold_explicit = size_of__panic_cold_explicit'

assume
val size_of_val': #v_T: Type0 -> v_val: v_T -> usize

unfold
let size_of_val (#v_T: Type0) = size_of_val' #v_T

assume
val size_of_val__panic_cold_explicit': Prims.unit -> Rust_primitives.Hax.t_Never

unfold
let size_of_val__panic_cold_explicit = size_of_val__panic_cold_explicit'

assume
val min_align_of': #v_T: Type0 -> Prims.unit -> usize

unfold
let min_align_of (#v_T: Type0) = min_align_of' #v_T

assume
val min_align_of__panic_cold_explicit': Prims.unit -> Rust_primitives.Hax.t_Never

unfold
let min_align_of__panic_cold_explicit = min_align_of__panic_cold_explicit'

assume
val min_align_of_val': #v_T: Type0 -> v_val: v_T -> usize

unfold
let min_align_of_val (#v_T: Type0) = min_align_of_val' #v_T

assume
val min_align_of_val__panic_cold_explicit': Prims.unit -> Rust_primitives.Hax.t_Never

unfold
let min_align_of_val__panic_cold_explicit = min_align_of_val__panic_cold_explicit'

assume
val align_of': #v_T: Type0 -> Prims.unit -> usize

unfold
let align_of (#v_T: Type0) = align_of' #v_T

assume
val align_of__panic_cold_explicit': Prims.unit -> Rust_primitives.Hax.t_Never

unfold
let align_of__panic_cold_explicit = align_of__panic_cold_explicit'

assume
val align_of_val': #v_T: Type0 -> v_val: v_T -> usize

unfold
let align_of_val (#v_T: Type0) = align_of_val' #v_T

assume
val align_of_val__panic_cold_explicit': Prims.unit -> Rust_primitives.Hax.t_Never

unfold
let align_of_val__panic_cold_explicit = align_of_val__panic_cold_explicit'

assume
val align_of_val_raw': #v_T: Type0 -> v_val: v_T -> usize

unfold
let align_of_val_raw (#v_T: Type0) = align_of_val_raw' #v_T

assume
val align_of_val_raw__panic_cold_explicit': Prims.unit -> Rust_primitives.Hax.t_Never

unfold
let align_of_val_raw__panic_cold_explicit = align_of_val_raw__panic_cold_explicit'

assume
val needs_drop': #v_T: Type0 -> Prims.unit -> bool

unfold
let needs_drop (#v_T: Type0) = needs_drop' #v_T

assume
val needs_drop__panic_cold_explicit': Prims.unit -> Rust_primitives.Hax.t_Never

unfold
let needs_drop__panic_cold_explicit = needs_drop__panic_cold_explicit'

assume
val uninitialized': #v_T: Type0 -> Prims.unit -> v_T

unfold
let uninitialized (#v_T: Type0) = uninitialized' #v_T

assume
val uninitialized__panic_cold_explicit': Prims.unit -> Rust_primitives.Hax.t_Never

unfold
let uninitialized__panic_cold_explicit = uninitialized__panic_cold_explicit'

assume
val swap': #v_T: Type0 -> x: v_T -> y: v_T -> (v_T & v_T)

unfold
let swap (#v_T: Type0) = swap' #v_T

assume
val swap__panic_cold_explicit': Prims.unit -> Rust_primitives.Hax.t_Never

unfold
let swap__panic_cold_explicit = swap__panic_cold_explicit'

assume
val replace': #v_T: Type0 -> dest: v_T -> src: v_T -> (v_T & v_T)

unfold
let replace (#v_T: Type0) = replace' #v_T

assume
val replace__panic_cold_explicit': Prims.unit -> Rust_primitives.Hax.t_Never

unfold
let replace__panic_cold_explicit = replace__panic_cold_explicit'

assume
val drop': #v_T: Type0 -> e_x: v_T -> Prims.unit

unfold
let drop (#v_T: Type0) = drop' #v_T

assume
val copy': #v_T: Type0 -> {| i0: Core_models.Marker.t_Copy v_T |} -> x: v_T -> v_T

unfold
let copy (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Marker.t_Copy v_T) =
  copy' #v_T #i0

assume
val transmute_copy': #v_Src: Type0 -> #v_Dst: Type0 -> src: v_Src -> v_Dst

unfold
let transmute_copy (#v_Src #v_Dst: Type0) = transmute_copy' #v_Src #v_Dst

assume
val transmute_copy__panic_cold_explicit': Prims.unit -> Rust_primitives.Hax.t_Never

unfold
let transmute_copy__panic_cold_explicit = transmute_copy__panic_cold_explicit'

assume
val variant_count': #v_T: Type0 -> Prims.unit -> usize

unfold
let variant_count (#v_T: Type0) = variant_count' #v_T

assume
val variant_count__panic_cold_explicit': Prims.unit -> Rust_primitives.Hax.t_Never

unfold
let variant_count__panic_cold_explicit = variant_count__panic_cold_explicit'

assume
val zeroed': #v_T: Type0 -> Prims.unit -> v_T

unfold
let zeroed (#v_T: Type0) = zeroed' #v_T

assume
val zeroed__panic_cold_explicit': Prims.unit -> Rust_primitives.Hax.t_Never

unfold
let zeroed__panic_cold_explicit = zeroed__panic_cold_explicit'
