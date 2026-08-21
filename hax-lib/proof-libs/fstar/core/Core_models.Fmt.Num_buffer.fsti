module Core_models.Fmt.Num_buffer
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::fmt::NumBufferTrait`]
class t_NumBufferTrait (v_Self: Type0) = { f_BUF_SIZE:usize }

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_NumBufferTrait_for_u8:t_NumBufferTrait u8

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_NumBufferTrait_for_i8:t_NumBufferTrait i8

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_NumBufferTrait_for_u16:t_NumBufferTrait u16

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_NumBufferTrait_for_i16:t_NumBufferTrait i16

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_NumBufferTrait_for_u32:t_NumBufferTrait u32

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_NumBufferTrait_for_i32:t_NumBufferTrait i32

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_NumBufferTrait_for_u64:t_NumBufferTrait u64

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_NumBufferTrait_for_i64:t_NumBufferTrait i64

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_NumBufferTrait_for_u128:t_NumBufferTrait u128

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_NumBufferTrait_for_i128:t_NumBufferTrait i128

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_NumBufferTrait_for_usize:t_NumBufferTrait usize

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_NumBufferTrait_for_isize:t_NumBufferTrait isize

/// See [`std::fmt::NumBuffer`]
/// Real `core` holds `[MaybeUninit<u8>; 40]`; the model has no `MaybeUninit`, so
/// the bytes are zeroed instead. The length is the same 40 real `core` uses (it
/// does not depend on `T::BUF_SIZE`), which is what `capacity` reports.
type t_NumBuffer (v_T: Type0) {| i0: t_NumBufferTrait v_T |} = {
  f_buf:t_Array u8 (mk_usize 40);
  f_phantom:Core_models.Marker.t_PhantomData v_T
}

/// See [`std::fmt::NumBuffer::new`]
val impl__new: #v_T: Type0 -> {| i0: t_NumBufferTrait v_T |} -> Prims.unit
  -> Prims.Pure (t_NumBuffer v_T) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::fmt::NumBuffer::capacity`]
val impl__capacity (#v_T: Type0) {| i0: t_NumBufferTrait v_T |} (self: t_NumBuffer v_T)
    : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)
