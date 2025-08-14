module Core.Mem.Maybe_uninit
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul


[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl (#v_T: Type0) {| i0: Core.Marker.t_Sized v_T |} {| i1: Core.Marker.t_Copy v_T |}
    : Core.Clone.t_Clone (t_MaybeUninit v_T)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_9 (#v_T: Type0) {| i0: Core.Marker.t_Sized v_T |} {| i1: Core.Marker.t_Copy v_T |}
    : Core.Marker.t_Copy (t_MaybeUninit v_T)

val f_clone__impl__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_1 (#v_T: Type0) {| i0: Core.Marker.t_Sized v_T |} : Core.Fmt.t_Debug (t_MaybeUninit v_T)

val f_fmt__impl_1__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val impl_2__new (#v_T: Type0) {| i0: Core.Marker.t_Sized v_T |} (v_val: v_T)
    : Prims.Pure (t_MaybeUninit v_T) Prims.l_True (fun _ -> Prims.l_True)

val impl_2__uninit: #v_T: Type0 -> {| i0: Core.Marker.t_Sized v_T |} -> Prims.unit
  -> Prims.Pure (t_MaybeUninit v_T) Prims.l_True (fun _ -> Prims.l_True)

val impl_2__zeroed: #v_T: Type0 -> {| i0: Core.Marker.t_Sized v_T |} -> Prims.unit
  -> Prims.Pure (t_MaybeUninit v_T) Prims.l_True (fun _ -> Prims.l_True)

val impl_2__write
      (#v_T: Type0)
      {| i0: Core.Marker.t_Sized v_T |}
      (self: t_MaybeUninit v_T)
      (v_val: v_T)
    : Prims.Pure (t_MaybeUninit v_T & Rust_primitives.Hax.t_MutRef v_T)
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl_2__as_ptr (#v_T: Type0) {| i0: Core.Marker.t_Sized v_T |} (self: t_MaybeUninit v_T)
    : Prims.Pure Rust_primitives.Hax.failure Prims.l_True (fun _ -> Prims.l_True)

val impl_2__as_mut_ptr (#v_T: Type0) {| i0: Core.Marker.t_Sized v_T |} (self: t_MaybeUninit v_T)
    : Prims.Pure (t_MaybeUninit v_T & Rust_primitives.Hax.failure)
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl_2__assume_init (#v_T: Type0) {| i0: Core.Marker.t_Sized v_T |} (self: t_MaybeUninit v_T)
    : Prims.Pure v_T Prims.l_True (fun _ -> Prims.l_True)

val impl_2__assume_init_read
      (#v_T: Type0)
      {| i0: Core.Marker.t_Sized v_T |}
      (self: t_MaybeUninit v_T)
    : Prims.Pure v_T Prims.l_True (fun _ -> Prims.l_True)

val impl_2__assume_init_drop
      (#v_T: Type0)
      {| i0: Core.Marker.t_Sized v_T |}
      (self: t_MaybeUninit v_T)
    : Prims.Pure (t_MaybeUninit v_T) Prims.l_True (fun _ -> Prims.l_True)

val impl_2__assume_init_ref
      (#v_T: Type0)
      {| i0: Core.Marker.t_Sized v_T |}
      (self: t_MaybeUninit v_T)
    : Prims.Pure v_T Prims.l_True (fun _ -> Prims.l_True)

val impl_2__assume_init_mut
      (#v_T: Type0)
      {| i0: Core.Marker.t_Sized v_T |}
      (self: t_MaybeUninit v_T)
    : Prims.Pure (t_MaybeUninit v_T & Rust_primitives.Hax.t_MutRef v_T)
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl_2__array_assume_init
      (#v_T: Type0)
      (v_N: usize)
      {| i0: Core.Marker.t_Sized v_T |}
      (array: t_Array (t_MaybeUninit v_T) v_N)
    : Prims.Pure (t_Array v_T v_N) Prims.l_True (fun _ -> Prims.l_True)

val impl_2__as_bytes (#v_T: Type0) {| i0: Core.Marker.t_Sized v_T |} (self: t_MaybeUninit v_T)
    : Prims.Pure (t_Slice (t_MaybeUninit u8)) Prims.l_True (fun _ -> Prims.l_True)

val impl_2__as_bytes_mut (#v_T: Type0) {| i0: Core.Marker.t_Sized v_T |} (self: t_MaybeUninit v_T)
    : Prims.Pure (t_MaybeUninit v_T & Rust_primitives.Hax.t_MutRef (t_Slice (t_MaybeUninit u8)))
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl_2__slice_assume_init_ref
      (#v_T: Type0)
      {| i0: Core.Marker.t_Sized v_T |}
      (slice: t_Slice (t_MaybeUninit v_T))
    : Prims.Pure (t_Slice v_T) Prims.l_True (fun _ -> Prims.l_True)

val impl_2__slice_assume_init_mut
      (#v_T: Type0)
      {| i0: Core.Marker.t_Sized v_T |}
      (slice: t_Slice (t_MaybeUninit v_T))
    : Prims.Pure (t_Slice (t_MaybeUninit v_T) & Rust_primitives.Hax.t_MutRef (t_Slice v_T))
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl_2__slice_as_ptr
      (#v_T: Type0)
      {| i0: Core.Marker.t_Sized v_T |}
      (this: t_Slice (t_MaybeUninit v_T))
    : Prims.Pure Rust_primitives.Hax.failure Prims.l_True (fun _ -> Prims.l_True)

val impl_2__slice_as_mut_ptr
      (#v_T: Type0)
      {| i0: Core.Marker.t_Sized v_T |}
      (this: t_Slice (t_MaybeUninit v_T))
    : Prims.Pure (t_Slice (t_MaybeUninit v_T) & Rust_primitives.Hax.failure)
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl_2__copy_from_slice
      (#v_T: Type0)
      {| i0: Core.Marker.t_Sized v_T |}
      {| i1: Core.Marker.t_Copy v_T |}
      (this: t_Slice (t_MaybeUninit v_T))
      (src: t_Slice v_T)
    : Prims.Pure (t_Slice (t_MaybeUninit v_T) & Rust_primitives.Hax.t_MutRef (t_Slice v_T))
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl_2__clone_from_slice
      (#v_T: Type0)
      {| i0: Core.Marker.t_Sized v_T |}
      {| i2: Core.Clone.t_Clone v_T |}
      (this: t_Slice (t_MaybeUninit v_T))
      (src: t_Slice v_T)
    : Prims.Pure (t_Slice (t_MaybeUninit v_T) & Rust_primitives.Hax.t_MutRef (t_Slice v_T))
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl_2__fill
      (#v_T: Type0)
      {| i0: Core.Marker.t_Sized v_T |}
      {| i2: Core.Clone.t_Clone v_T |}
      (this: t_Slice (t_MaybeUninit v_T))
      (value: v_T)
    : Prims.Pure (t_Slice (t_MaybeUninit v_T) & Rust_primitives.Hax.t_MutRef (t_Slice v_T))
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl_2__fill_with
      (#v_T #v_F: Type0)
      {| i0: Core.Marker.t_Sized v_T |}
      {| i3: Core.Marker.t_Sized v_F |}
      {| i4: Core.Ops.Function.t_FnMut v_F Prims.unit |}
      (this: t_Slice (t_MaybeUninit v_T))
      (f: v_F)
    : Prims.Pure (t_Slice (t_MaybeUninit v_T) & Rust_primitives.Hax.t_MutRef (t_Slice v_T))
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl_2__fill_from
      (#v_T #v_I: Type0)
      {| i0: Core.Marker.t_Sized v_T |}
      {| i5: Core.Marker.t_Sized v_I |}
      {| i6: Core.Iter.Traits.Collect.t_IntoIterator v_I |}
      (this: t_Slice (t_MaybeUninit v_T))
      (it: v_I)
    : Prims.Pure
      (t_Slice (t_MaybeUninit v_T) &
        (Rust_primitives.Hax.t_MutRef (t_Slice v_T) &
          Rust_primitives.Hax.t_MutRef (t_Slice (t_MaybeUninit v_T))))
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl_2__slice_as_bytes
      (#v_T: Type0)
      {| i0: Core.Marker.t_Sized v_T |}
      (this: t_Slice (t_MaybeUninit v_T))
    : Prims.Pure (t_Slice (t_MaybeUninit u8)) Prims.l_True (fun _ -> Prims.l_True)

val impl_2__slice_as_bytes_mut
      (#v_T: Type0)
      {| i0: Core.Marker.t_Sized v_T |}
      (this: t_Slice (t_MaybeUninit v_T))
    : Prims.Pure
      (t_Slice (t_MaybeUninit v_T) & Rust_primitives.Hax.t_MutRef (t_Slice (t_MaybeUninit u8)))
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl_2__assume_init_drop__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val impl_2__copy_from_slice__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val impl_2__clone_from_slice__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val impl_2__fill__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val impl_2__fill_with__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val impl_2__fill_from__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val impl_2__slice_as_bytes__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val impl_2__slice_as_bytes_mut__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val impl_3__write_copy_of_slice
      (#v_T: Type0)
      {| i0: Core.Marker.t_Sized v_T |}
      {| i1: Core.Marker.t_Copy v_T |}
      (self: t_Slice (t_MaybeUninit v_T))
      (src: t_Slice v_T)
    : Prims.Pure (t_Slice (t_MaybeUninit v_T) & Rust_primitives.Hax.t_MutRef (t_Slice v_T))
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl_3__write_clone_of_slice
      (#v_T: Type0)
      {| i0: Core.Marker.t_Sized v_T |}
      {| i2: Core.Clone.t_Clone v_T |}
      (self: t_Slice (t_MaybeUninit v_T))
      (src: t_Slice v_T)
    : Prims.Pure (t_Slice (t_MaybeUninit v_T) & Rust_primitives.Hax.t_MutRef (t_Slice v_T))
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl_3__write_filled
      (#v_T: Type0)
      {| i0: Core.Marker.t_Sized v_T |}
      {| i2: Core.Clone.t_Clone v_T |}
      (self: t_Slice (t_MaybeUninit v_T))
      (value: v_T)
    : Prims.Pure (t_Slice (t_MaybeUninit v_T) & Rust_primitives.Hax.t_MutRef (t_Slice v_T))
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl_3__write_with
      (#v_T #v_F: Type0)
      {| i0: Core.Marker.t_Sized v_T |}
      {| i3: Core.Marker.t_Sized v_F |}
      {| i4: Core.Ops.Function.t_FnMut v_F usize |}
      (self: t_Slice (t_MaybeUninit v_T))
      (f: v_F)
    : Prims.Pure (t_Slice (t_MaybeUninit v_T) & Rust_primitives.Hax.t_MutRef (t_Slice v_T))
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl_3__write_iter
      (#v_T #v_I: Type0)
      {| i0: Core.Marker.t_Sized v_T |}
      {| i5: Core.Marker.t_Sized v_I |}
      {| i6: Core.Iter.Traits.Collect.t_IntoIterator v_I |}
      (self: t_Slice (t_MaybeUninit v_T))
      (it: v_I)
    : Prims.Pure
      (t_Slice (t_MaybeUninit v_T) &
        (Rust_primitives.Hax.t_MutRef (t_Slice v_T) &
          Rust_primitives.Hax.t_MutRef (t_Slice (t_MaybeUninit v_T))))
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl_3__as_bytes
      (#v_T: Type0)
      {| i0: Core.Marker.t_Sized v_T |}
      (self: t_Slice (t_MaybeUninit v_T))
    : Prims.Pure (t_Slice (t_MaybeUninit u8)) Prims.l_True (fun _ -> Prims.l_True)

val impl_3__as_bytes_mut
      (#v_T: Type0)
      {| i0: Core.Marker.t_Sized v_T |}
      (self: t_Slice (t_MaybeUninit v_T))
    : Prims.Pure
      (t_Slice (t_MaybeUninit v_T) & Rust_primitives.Hax.t_MutRef (t_Slice (t_MaybeUninit u8)))
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl_3__assume_init_drop
      (#v_T: Type0)
      {| i0: Core.Marker.t_Sized v_T |}
      (self: t_Slice (t_MaybeUninit v_T))
    : Prims.Pure (t_Slice (t_MaybeUninit v_T)) Prims.l_True (fun _ -> Prims.l_True)

val impl_3__assume_init_ref
      (#v_T: Type0)
      {| i0: Core.Marker.t_Sized v_T |}
      (self: t_Slice (t_MaybeUninit v_T))
    : Prims.Pure (t_Slice v_T) Prims.l_True (fun _ -> Prims.l_True)

val impl_3__assume_init_mut
      (#v_T: Type0)
      {| i0: Core.Marker.t_Sized v_T |}
      (self: t_Slice (t_MaybeUninit v_T))
    : Prims.Pure (t_Slice (t_MaybeUninit v_T) & Rust_primitives.Hax.t_MutRef (t_Slice v_T))
      Prims.l_True
      (fun _ -> Prims.l_True)

val impl_4__transpose
      (#v_T: Type0)
      (v_N: usize)
      {| i0: Core.Marker.t_Sized v_T |}
      (self: t_MaybeUninit (t_Array v_T v_N))
    : Prims.Pure (t_Array (t_MaybeUninit v_T) v_N) Prims.l_True (fun _ -> Prims.l_True)

val impl_5__transpose
      (#v_T: Type0)
      (v_N: usize)
      {| i0: Core.Marker.t_Sized v_T |}
      (self: t_Array (t_MaybeUninit v_T) v_N)
    : Prims.Pure (t_MaybeUninit (t_Array v_T v_N)) Prims.l_True (fun _ -> Prims.l_True)

type t_Guard (v_T: Type0) {| i0: Core.Marker.t_Sized v_T |} = {
  f_slice:Rust_primitives.Hax.t_MutRef (t_Slice (t_MaybeUninit v_T));
  f_initialized:usize
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_6 (#v_T: Type0) {| i0: Core.Marker.t_Sized v_T |} : Core.Ops.Drop.t_Drop (t_Guard v_T)

val f_drop__impl_6__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

class t_SpecFill (v_Self: Type0) (v_T: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_15671470021555116719:Core.Marker.t_Sized v_T;
  f_spec_fill_pre:v_Self -> v_T -> Type0;
  f_spec_fill_post:v_Self -> v_T -> v_Self -> Type0;
  f_spec_fill:x0: v_Self -> x1: v_T
    -> Prims.Pure v_Self (f_spec_fill_pre x0 x1) (fun result -> f_spec_fill_post x0 x1 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_7 (#v_T: Type0) {| i0: Core.Marker.t_Sized v_T |} {| i1: Core.Clone.t_Clone v_T |}
    : t_SpecFill (t_Slice (t_MaybeUninit v_T)) v_T

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_8 (#v_T: Type0) {| i0: Core.Marker.t_Sized v_T |} {| i1: Core.Marker.t_Copy v_T |}
    : t_SpecFill (t_Slice (t_MaybeUninit v_T)) v_T
