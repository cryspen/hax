module Core_models.Ops.Range
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

type t_RangeTo (v_T: Type0) = { f_end:v_T }

type t_RangeFrom (v_T: Type0) = { f_start:v_T }

type t_Range (v_T: Type0) = {
  f_start:v_T;
  f_end:v_T
}

type t_RangeFull = | RangeFull : t_RangeFull

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_T: Type0) : Core_models.Ops.Index.t_Index (t_Slice v_T) (t_Range usize) =
  {
    f_Output = t_Slice v_T;
    f_index_pre
    =
    (fun (self_: t_Slice v_T) (i: t_Range usize) ->
        i.f_start <=. i.f_end && i.f_end <=. (Core_models.Slice.impl__len #v_T self_ <: usize));
    f_index_post = (fun (self: t_Slice v_T) (i: t_Range usize) (out: t_Slice v_T) -> true);
    f_index
    =
    fun (self: t_Slice v_T) (i: t_Range usize) ->
      Rust_primitives.Slice.slice_slice #v_T self i.f_start i.f_end
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1 (#v_T: Type0) : Core_models.Ops.Index.t_Index (t_Slice v_T) (t_RangeTo usize) =
  {
    f_Output = t_Slice v_T;
    f_index_pre
    =
    (fun (self_: t_Slice v_T) (i: t_RangeTo usize) ->
        i.f_end <=. (Core_models.Slice.impl__len #v_T self_ <: usize));
    f_index_post = (fun (self: t_Slice v_T) (i: t_RangeTo usize) (out: t_Slice v_T) -> true);
    f_index
    =
    fun (self: t_Slice v_T) (i: t_RangeTo usize) ->
      Rust_primitives.Slice.slice_slice #v_T self (mk_usize 0) i.f_end
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2 (#v_T: Type0) : Core_models.Ops.Index.t_Index (t_Slice v_T) (t_RangeFrom usize) =
  {
    f_Output = t_Slice v_T;
    f_index_pre
    =
    (fun (self_: t_Slice v_T) (i: t_RangeFrom usize) ->
        i.f_start <=. (Core_models.Slice.impl__len #v_T self_ <: usize));
    f_index_post = (fun (self: t_Slice v_T) (i: t_RangeFrom usize) (out: t_Slice v_T) -> true);
    f_index
    =
    fun (self: t_Slice v_T) (i: t_RangeFrom usize) ->
      Rust_primitives.Slice.slice_slice #v_T
        self
        i.f_start
        (Rust_primitives.Slice.slice_length #v_T self <: usize)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3 (#v_T: Type0) : Core_models.Ops.Index.t_Index (t_Slice v_T) t_RangeFull =
  {
    f_Output = t_Slice v_T;
    f_index_pre = (fun (self: t_Slice v_T) (i: t_RangeFull) -> true);
    f_index_post = (fun (self: t_Slice v_T) (i: t_RangeFull) (out: t_Slice v_T) -> true);
    f_index
    =
    fun (self: t_Slice v_T) (i: t_RangeFull) ->
      Rust_primitives.Slice.slice_slice #v_T
        self
        (mk_usize 0)
        (Rust_primitives.Slice.slice_length #v_T self <: usize)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4 (#v_T: Type0) (v_N: usize)
    : Core_models.Ops.Index.t_Index (t_Array v_T v_N) (t_Range usize) =
  {
    f_Output = t_Slice v_T;
    f_index_pre
    =
    (fun (self_: t_Array v_T v_N) (i: t_Range usize) ->
        i.f_start <=. i.f_end &&
        i.f_end <=. (Core_models.Slice.impl__len #v_T (self_ <: t_Slice v_T) <: usize));
    f_index_post = (fun (self: t_Array v_T v_N) (i: t_Range usize) (out: t_Slice v_T) -> true);
    f_index
    =
    fun (self: t_Array v_T v_N) (i: t_Range usize) ->
      Rust_primitives.Slice.array_slice #v_T v_N self i.f_start i.f_end
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5 (#v_T: Type0) (v_N: usize)
    : Core_models.Ops.Index.t_Index (t_Array v_T v_N) (t_RangeTo usize) =
  {
    f_Output = t_Slice v_T;
    f_index_pre
    =
    (fun (self_: t_Array v_T v_N) (i: t_RangeTo usize) ->
        i.f_end <=. (Core_models.Slice.impl__len #v_T (self_ <: t_Slice v_T) <: usize));
    f_index_post = (fun (self: t_Array v_T v_N) (i: t_RangeTo usize) (out: t_Slice v_T) -> true);
    f_index
    =
    fun (self: t_Array v_T v_N) (i: t_RangeTo usize) ->
      Rust_primitives.Slice.array_slice #v_T v_N self (mk_usize 0) i.f_end
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6 (#v_T: Type0) (v_N: usize)
    : Core_models.Ops.Index.t_Index (t_Array v_T v_N) (t_RangeFrom usize) =
  {
    f_Output = t_Slice v_T;
    f_index_pre
    =
    (fun (self_: t_Array v_T v_N) (i: t_RangeFrom usize) ->
        i.f_start <=. (Core_models.Slice.impl__len #v_T (self_ <: t_Slice v_T) <: usize));
    f_index_post = (fun (self: t_Array v_T v_N) (i: t_RangeFrom usize) (out: t_Slice v_T) -> true);
    f_index
    =
    fun (self: t_Array v_T v_N) (i: t_RangeFrom usize) ->
      Rust_primitives.Slice.array_slice #v_T v_N self i.f_start v_N
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7 (#v_T: Type0) (v_N: usize) : Core_models.Ops.Index.t_Index (t_Array v_T v_N) t_RangeFull =
  {
    f_Output = t_Slice v_T;
    f_index_pre = (fun (self: t_Array v_T v_N) (i: t_RangeFull) -> true);
    f_index_post = (fun (self: t_Array v_T v_N) (i: t_RangeFull) (out: t_Slice v_T) -> true);
    f_index
    =
    fun (self: t_Array v_T v_N) (i: t_RangeFull) ->
      Rust_primitives.Slice.array_slice #v_T v_N self (mk_usize 0) v_N
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8: Core_models.Iter.Traits.Iterator.t_Iterator (t_Range u8) =
  {
    f_Item = u8;
    f_next_pre = (fun (self: t_Range u8) -> true);
    f_next_post
    =
    (fun (self: t_Range u8) (out: (t_Range u8 & Core_models.Option.t_Option u8)) -> true);
    f_next
    =
    fun (self: t_Range u8) ->
      let (self: t_Range u8), (hax_temp_output: Core_models.Option.t_Option u8) =
        if self.f_start >=. self.f_end
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option u8)
          <:
          (t_Range u8 & Core_models.Option.t_Option u8)
        else
          let res:u8 = self.f_start in
          let self:t_Range u8 = { self with f_start = self.f_start +! mk_u8 1 } <: t_Range u8 in
          self, (Core_models.Option.Option_Some res <: Core_models.Option.t_Option u8)
          <:
          (t_Range u8 & Core_models.Option.t_Option u8)
      in
      self, hax_temp_output <: (t_Range u8 & Core_models.Option.t_Option u8)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9: Core_models.Iter.Traits.Iterator.t_Iterator (t_Range u16) =
  {
    f_Item = u16;
    f_next_pre = (fun (self: t_Range u16) -> true);
    f_next_post
    =
    (fun (self: t_Range u16) (out: (t_Range u16 & Core_models.Option.t_Option u16)) -> true);
    f_next
    =
    fun (self: t_Range u16) ->
      let (self: t_Range u16), (hax_temp_output: Core_models.Option.t_Option u16) =
        if self.f_start >=. self.f_end
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option u16)
          <:
          (t_Range u16 & Core_models.Option.t_Option u16)
        else
          let res:u16 = self.f_start in
          let self:t_Range u16 = { self with f_start = self.f_start +! mk_u16 1 } <: t_Range u16 in
          self, (Core_models.Option.Option_Some res <: Core_models.Option.t_Option u16)
          <:
          (t_Range u16 & Core_models.Option.t_Option u16)
      in
      self, hax_temp_output <: (t_Range u16 & Core_models.Option.t_Option u16)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10: Core_models.Iter.Traits.Iterator.t_Iterator (t_Range u32) =
  {
    f_Item = u32;
    f_next_pre = (fun (self: t_Range u32) -> true);
    f_next_post
    =
    (fun (self: t_Range u32) (out: (t_Range u32 & Core_models.Option.t_Option u32)) -> true);
    f_next
    =
    fun (self: t_Range u32) ->
      let (self: t_Range u32), (hax_temp_output: Core_models.Option.t_Option u32) =
        if self.f_start >=. self.f_end
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option u32)
          <:
          (t_Range u32 & Core_models.Option.t_Option u32)
        else
          let res:u32 = self.f_start in
          let self:t_Range u32 = { self with f_start = self.f_start +! mk_u32 1 } <: t_Range u32 in
          self, (Core_models.Option.Option_Some res <: Core_models.Option.t_Option u32)
          <:
          (t_Range u32 & Core_models.Option.t_Option u32)
      in
      self, hax_temp_output <: (t_Range u32 & Core_models.Option.t_Option u32)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_11: Core_models.Iter.Traits.Iterator.t_Iterator (t_Range u64) =
  {
    f_Item = u64;
    f_next_pre = (fun (self: t_Range u64) -> true);
    f_next_post
    =
    (fun (self: t_Range u64) (out: (t_Range u64 & Core_models.Option.t_Option u64)) -> true);
    f_next
    =
    fun (self: t_Range u64) ->
      let (self: t_Range u64), (hax_temp_output: Core_models.Option.t_Option u64) =
        if self.f_start >=. self.f_end
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option u64)
          <:
          (t_Range u64 & Core_models.Option.t_Option u64)
        else
          let res:u64 = self.f_start in
          let self:t_Range u64 = { self with f_start = self.f_start +! mk_u64 1 } <: t_Range u64 in
          self, (Core_models.Option.Option_Some res <: Core_models.Option.t_Option u64)
          <:
          (t_Range u64 & Core_models.Option.t_Option u64)
      in
      self, hax_temp_output <: (t_Range u64 & Core_models.Option.t_Option u64)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_12: Core_models.Iter.Traits.Iterator.t_Iterator (t_Range u128) =
  {
    f_Item = u128;
    f_next_pre = (fun (self: t_Range u128) -> true);
    f_next_post
    =
    (fun (self: t_Range u128) (out: (t_Range u128 & Core_models.Option.t_Option u128)) -> true);
    f_next
    =
    fun (self: t_Range u128) ->
      let (self: t_Range u128), (hax_temp_output: Core_models.Option.t_Option u128) =
        if self.f_start >=. self.f_end
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option u128)
          <:
          (t_Range u128 & Core_models.Option.t_Option u128)
        else
          let res:u128 = self.f_start in
          let self:t_Range u128 =
            { self with f_start = self.f_start +! mk_u128 1 } <: t_Range u128
          in
          self, (Core_models.Option.Option_Some res <: Core_models.Option.t_Option u128)
          <:
          (t_Range u128 & Core_models.Option.t_Option u128)
      in
      self, hax_temp_output <: (t_Range u128 & Core_models.Option.t_Option u128)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_13: Core_models.Iter.Traits.Iterator.t_Iterator (t_Range usize) =
  {
    f_Item = usize;
    f_next_pre = (fun (self: t_Range usize) -> true);
    f_next_post
    =
    (fun (self: t_Range usize) (out: (t_Range usize & Core_models.Option.t_Option usize)) -> true);
    f_next
    =
    fun (self: t_Range usize) ->
      let (self: t_Range usize), (hax_temp_output: Core_models.Option.t_Option usize) =
        if self.f_start >=. self.f_end
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option usize)
          <:
          (t_Range usize & Core_models.Option.t_Option usize)
        else
          let res:usize = self.f_start in
          let self:t_Range usize =
            { self with f_start = self.f_start +! mk_usize 1 } <: t_Range usize
          in
          self, (Core_models.Option.Option_Some res <: Core_models.Option.t_Option usize)
          <:
          (t_Range usize & Core_models.Option.t_Option usize)
      in
      self, hax_temp_output <: (t_Range usize & Core_models.Option.t_Option usize)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_14: Core_models.Iter.Traits.Iterator.t_Iterator (t_Range i8) =
  {
    f_Item = i8;
    f_next_pre = (fun (self: t_Range i8) -> true);
    f_next_post
    =
    (fun (self: t_Range i8) (out: (t_Range i8 & Core_models.Option.t_Option i8)) -> true);
    f_next
    =
    fun (self: t_Range i8) ->
      let (self: t_Range i8), (hax_temp_output: Core_models.Option.t_Option i8) =
        if self.f_start >=. self.f_end
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option i8)
          <:
          (t_Range i8 & Core_models.Option.t_Option i8)
        else
          let res:i8 = self.f_start in
          let self:t_Range i8 = { self with f_start = self.f_start +! mk_i8 1 } <: t_Range i8 in
          self, (Core_models.Option.Option_Some res <: Core_models.Option.t_Option i8)
          <:
          (t_Range i8 & Core_models.Option.t_Option i8)
      in
      self, hax_temp_output <: (t_Range i8 & Core_models.Option.t_Option i8)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_15: Core_models.Iter.Traits.Iterator.t_Iterator (t_Range i16) =
  {
    f_Item = i16;
    f_next_pre = (fun (self: t_Range i16) -> true);
    f_next_post
    =
    (fun (self: t_Range i16) (out: (t_Range i16 & Core_models.Option.t_Option i16)) -> true);
    f_next
    =
    fun (self: t_Range i16) ->
      let (self: t_Range i16), (hax_temp_output: Core_models.Option.t_Option i16) =
        if self.f_start >=. self.f_end
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option i16)
          <:
          (t_Range i16 & Core_models.Option.t_Option i16)
        else
          let res:i16 = self.f_start in
          let self:t_Range i16 = { self with f_start = self.f_start +! mk_i16 1 } <: t_Range i16 in
          self, (Core_models.Option.Option_Some res <: Core_models.Option.t_Option i16)
          <:
          (t_Range i16 & Core_models.Option.t_Option i16)
      in
      self, hax_temp_output <: (t_Range i16 & Core_models.Option.t_Option i16)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_16: Core_models.Iter.Traits.Iterator.t_Iterator (t_Range i32) =
  {
    f_Item = i32;
    f_next_pre = (fun (self: t_Range i32) -> true);
    f_next_post
    =
    (fun (self: t_Range i32) (out: (t_Range i32 & Core_models.Option.t_Option i32)) -> true);
    f_next
    =
    fun (self: t_Range i32) ->
      let (self: t_Range i32), (hax_temp_output: Core_models.Option.t_Option i32) =
        if self.f_start >=. self.f_end
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option i32)
          <:
          (t_Range i32 & Core_models.Option.t_Option i32)
        else
          let res:i32 = self.f_start in
          let self:t_Range i32 = { self with f_start = self.f_start +! mk_i32 1 } <: t_Range i32 in
          self, (Core_models.Option.Option_Some res <: Core_models.Option.t_Option i32)
          <:
          (t_Range i32 & Core_models.Option.t_Option i32)
      in
      self, hax_temp_output <: (t_Range i32 & Core_models.Option.t_Option i32)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_17: Core_models.Iter.Traits.Iterator.t_Iterator (t_Range i64) =
  {
    f_Item = i64;
    f_next_pre = (fun (self: t_Range i64) -> true);
    f_next_post
    =
    (fun (self: t_Range i64) (out: (t_Range i64 & Core_models.Option.t_Option i64)) -> true);
    f_next
    =
    fun (self: t_Range i64) ->
      let (self: t_Range i64), (hax_temp_output: Core_models.Option.t_Option i64) =
        if self.f_start >=. self.f_end
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option i64)
          <:
          (t_Range i64 & Core_models.Option.t_Option i64)
        else
          let res:i64 = self.f_start in
          let self:t_Range i64 = { self with f_start = self.f_start +! mk_i64 1 } <: t_Range i64 in
          self, (Core_models.Option.Option_Some res <: Core_models.Option.t_Option i64)
          <:
          (t_Range i64 & Core_models.Option.t_Option i64)
      in
      self, hax_temp_output <: (t_Range i64 & Core_models.Option.t_Option i64)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_18: Core_models.Iter.Traits.Iterator.t_Iterator (t_Range i128) =
  {
    f_Item = i128;
    f_next_pre = (fun (self: t_Range i128) -> true);
    f_next_post
    =
    (fun (self: t_Range i128) (out: (t_Range i128 & Core_models.Option.t_Option i128)) -> true);
    f_next
    =
    fun (self: t_Range i128) ->
      let (self: t_Range i128), (hax_temp_output: Core_models.Option.t_Option i128) =
        if self.f_start >=. self.f_end
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option i128)
          <:
          (t_Range i128 & Core_models.Option.t_Option i128)
        else
          let res:i128 = self.f_start in
          let self:t_Range i128 =
            { self with f_start = self.f_start +! mk_i128 1 } <: t_Range i128
          in
          self, (Core_models.Option.Option_Some res <: Core_models.Option.t_Option i128)
          <:
          (t_Range i128 & Core_models.Option.t_Option i128)
      in
      self, hax_temp_output <: (t_Range i128 & Core_models.Option.t_Option i128)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_19: Core_models.Iter.Traits.Iterator.t_Iterator (t_Range isize) =
  {
    f_Item = isize;
    f_next_pre = (fun (self: t_Range isize) -> true);
    f_next_post
    =
    (fun (self: t_Range isize) (out: (t_Range isize & Core_models.Option.t_Option isize)) -> true);
    f_next
    =
    fun (self: t_Range isize) ->
      let (self: t_Range isize), (hax_temp_output: Core_models.Option.t_Option isize) =
        if self.f_start >=. self.f_end
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option isize)
          <:
          (t_Range isize & Core_models.Option.t_Option isize)
        else
          let res:isize = self.f_start in
          let self:t_Range isize =
            { self with f_start = self.f_start +! mk_isize 1 } <: t_Range isize
          in
          self, (Core_models.Option.Option_Some res <: Core_models.Option.t_Option isize)
          <:
          (t_Range isize & Core_models.Option.t_Option isize)
      in
      self, hax_temp_output <: (t_Range isize & Core_models.Option.t_Option isize)
  }
