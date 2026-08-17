module Core_models.Iter.Ends
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Core_models.Iter.Traits.Double_ended.t_DoubleEndedIterator
(Core_models.Ops.Range.t_Range u8) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_next_back_pre = (fun (self: Core_models.Ops.Range.t_Range u8) -> true);
    f_next_back_post
    =
    (fun
        (self: Core_models.Ops.Range.t_Range u8)
        (out: (Core_models.Ops.Range.t_Range u8 & Core_models.Option.t_Option u8))
        ->
        true);
    f_next_back
    =
    fun (self: Core_models.Ops.Range.t_Range u8) ->
      let
      (self: Core_models.Ops.Range.t_Range u8), (hax_temp_output: Core_models.Option.t_Option u8) =
        if self.Core_models.Ops.Range.f_start >=. self.Core_models.Ops.Range.f_end
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option u8)
          <:
          (Core_models.Ops.Range.t_Range u8 & Core_models.Option.t_Option u8)
        else
          let self:Core_models.Ops.Range.t_Range u8 =
            { self with Core_models.Ops.Range.f_end = self.Core_models.Ops.Range.f_end -! mk_u8 1 }
            <:
            Core_models.Ops.Range.t_Range u8
          in
          self,
          (Core_models.Option.Option_Some self.Core_models.Ops.Range.f_end
            <:
            Core_models.Option.t_Option u8)
          <:
          (Core_models.Ops.Range.t_Range u8 & Core_models.Option.t_Option u8)
      in
      self, hax_temp_output <: (Core_models.Ops.Range.t_Range u8 & Core_models.Option.t_Option u8)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: Core_models.Iter.Traits.Double_ended.t_DoubleEndedIterator
(Core_models.Ops.Range.t_Range u16) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_next_back_pre = (fun (self: Core_models.Ops.Range.t_Range u16) -> true);
    f_next_back_post
    =
    (fun
        (self: Core_models.Ops.Range.t_Range u16)
        (out: (Core_models.Ops.Range.t_Range u16 & Core_models.Option.t_Option u16))
        ->
        true);
    f_next_back
    =
    fun (self: Core_models.Ops.Range.t_Range u16) ->
      let
      (self: Core_models.Ops.Range.t_Range u16), (hax_temp_output: Core_models.Option.t_Option u16)
      =
        if self.Core_models.Ops.Range.f_start >=. self.Core_models.Ops.Range.f_end
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option u16)
          <:
          (Core_models.Ops.Range.t_Range u16 & Core_models.Option.t_Option u16)
        else
          let self:Core_models.Ops.Range.t_Range u16 =
            { self with Core_models.Ops.Range.f_end = self.Core_models.Ops.Range.f_end -! mk_u16 1 }
            <:
            Core_models.Ops.Range.t_Range u16
          in
          self,
          (Core_models.Option.Option_Some self.Core_models.Ops.Range.f_end
            <:
            Core_models.Option.t_Option u16)
          <:
          (Core_models.Ops.Range.t_Range u16 & Core_models.Option.t_Option u16)
      in
      self, hax_temp_output <: (Core_models.Ops.Range.t_Range u16 & Core_models.Option.t_Option u16)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4: Core_models.Iter.Traits.Double_ended.t_DoubleEndedIterator
(Core_models.Ops.Range.t_Range u32) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_next_back_pre = (fun (self: Core_models.Ops.Range.t_Range u32) -> true);
    f_next_back_post
    =
    (fun
        (self: Core_models.Ops.Range.t_Range u32)
        (out: (Core_models.Ops.Range.t_Range u32 & Core_models.Option.t_Option u32))
        ->
        true);
    f_next_back
    =
    fun (self: Core_models.Ops.Range.t_Range u32) ->
      let
      (self: Core_models.Ops.Range.t_Range u32), (hax_temp_output: Core_models.Option.t_Option u32)
      =
        if self.Core_models.Ops.Range.f_start >=. self.Core_models.Ops.Range.f_end
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option u32)
          <:
          (Core_models.Ops.Range.t_Range u32 & Core_models.Option.t_Option u32)
        else
          let self:Core_models.Ops.Range.t_Range u32 =
            { self with Core_models.Ops.Range.f_end = self.Core_models.Ops.Range.f_end -! mk_u32 1 }
            <:
            Core_models.Ops.Range.t_Range u32
          in
          self,
          (Core_models.Option.Option_Some self.Core_models.Ops.Range.f_end
            <:
            Core_models.Option.t_Option u32)
          <:
          (Core_models.Ops.Range.t_Range u32 & Core_models.Option.t_Option u32)
      in
      self, hax_temp_output <: (Core_models.Ops.Range.t_Range u32 & Core_models.Option.t_Option u32)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5: Core_models.Iter.Traits.Double_ended.t_DoubleEndedIterator
(Core_models.Ops.Range.t_Range u64) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_next_back_pre = (fun (self: Core_models.Ops.Range.t_Range u64) -> true);
    f_next_back_post
    =
    (fun
        (self: Core_models.Ops.Range.t_Range u64)
        (out: (Core_models.Ops.Range.t_Range u64 & Core_models.Option.t_Option u64))
        ->
        true);
    f_next_back
    =
    fun (self: Core_models.Ops.Range.t_Range u64) ->
      let
      (self: Core_models.Ops.Range.t_Range u64), (hax_temp_output: Core_models.Option.t_Option u64)
      =
        if self.Core_models.Ops.Range.f_start >=. self.Core_models.Ops.Range.f_end
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option u64)
          <:
          (Core_models.Ops.Range.t_Range u64 & Core_models.Option.t_Option u64)
        else
          let self:Core_models.Ops.Range.t_Range u64 =
            { self with Core_models.Ops.Range.f_end = self.Core_models.Ops.Range.f_end -! mk_u64 1 }
            <:
            Core_models.Ops.Range.t_Range u64
          in
          self,
          (Core_models.Option.Option_Some self.Core_models.Ops.Range.f_end
            <:
            Core_models.Option.t_Option u64)
          <:
          (Core_models.Ops.Range.t_Range u64 & Core_models.Option.t_Option u64)
      in
      self, hax_temp_output <: (Core_models.Ops.Range.t_Range u64 & Core_models.Option.t_Option u64)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6: Core_models.Iter.Traits.Double_ended.t_DoubleEndedIterator
(Core_models.Ops.Range.t_Range u128) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_next_back_pre = (fun (self: Core_models.Ops.Range.t_Range u128) -> true);
    f_next_back_post
    =
    (fun
        (self: Core_models.Ops.Range.t_Range u128)
        (out: (Core_models.Ops.Range.t_Range u128 & Core_models.Option.t_Option u128))
        ->
        true);
    f_next_back
    =
    fun (self: Core_models.Ops.Range.t_Range u128) ->
      let
      (self: Core_models.Ops.Range.t_Range u128),
      (hax_temp_output: Core_models.Option.t_Option u128) =
        if self.Core_models.Ops.Range.f_start >=. self.Core_models.Ops.Range.f_end
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option u128)
          <:
          (Core_models.Ops.Range.t_Range u128 & Core_models.Option.t_Option u128)
        else
          let self:Core_models.Ops.Range.t_Range u128 =
            {
              self with
              Core_models.Ops.Range.f_end = self.Core_models.Ops.Range.f_end -! mk_u128 1
            }
            <:
            Core_models.Ops.Range.t_Range u128
          in
          self,
          (Core_models.Option.Option_Some self.Core_models.Ops.Range.f_end
            <:
            Core_models.Option.t_Option u128)
          <:
          (Core_models.Ops.Range.t_Range u128 & Core_models.Option.t_Option u128)
      in
      self, hax_temp_output
      <:
      (Core_models.Ops.Range.t_Range u128 & Core_models.Option.t_Option u128)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7: Core_models.Iter.Traits.Double_ended.t_DoubleEndedIterator
(Core_models.Ops.Range.t_Range usize) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_next_back_pre = (fun (self: Core_models.Ops.Range.t_Range usize) -> true);
    f_next_back_post
    =
    (fun
        (self: Core_models.Ops.Range.t_Range usize)
        (out: (Core_models.Ops.Range.t_Range usize & Core_models.Option.t_Option usize))
        ->
        true);
    f_next_back
    =
    fun (self: Core_models.Ops.Range.t_Range usize) ->
      let
      (self: Core_models.Ops.Range.t_Range usize),
      (hax_temp_output: Core_models.Option.t_Option usize) =
        if self.Core_models.Ops.Range.f_start >=. self.Core_models.Ops.Range.f_end
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option usize)
          <:
          (Core_models.Ops.Range.t_Range usize & Core_models.Option.t_Option usize)
        else
          let self:Core_models.Ops.Range.t_Range usize =
            {
              self with
              Core_models.Ops.Range.f_end = self.Core_models.Ops.Range.f_end -! mk_usize 1
            }
            <:
            Core_models.Ops.Range.t_Range usize
          in
          self,
          (Core_models.Option.Option_Some self.Core_models.Ops.Range.f_end
            <:
            Core_models.Option.t_Option usize)
          <:
          (Core_models.Ops.Range.t_Range usize & Core_models.Option.t_Option usize)
      in
      self, hax_temp_output
      <:
      (Core_models.Ops.Range.t_Range usize & Core_models.Option.t_Option usize)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8: Core_models.Iter.Traits.Double_ended.t_DoubleEndedIterator
(Core_models.Ops.Range.t_Range i8) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_next_back_pre = (fun (self: Core_models.Ops.Range.t_Range i8) -> true);
    f_next_back_post
    =
    (fun
        (self: Core_models.Ops.Range.t_Range i8)
        (out: (Core_models.Ops.Range.t_Range i8 & Core_models.Option.t_Option i8))
        ->
        true);
    f_next_back
    =
    fun (self: Core_models.Ops.Range.t_Range i8) ->
      let
      (self: Core_models.Ops.Range.t_Range i8), (hax_temp_output: Core_models.Option.t_Option i8) =
        if self.Core_models.Ops.Range.f_start >=. self.Core_models.Ops.Range.f_end
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option i8)
          <:
          (Core_models.Ops.Range.t_Range i8 & Core_models.Option.t_Option i8)
        else
          let self:Core_models.Ops.Range.t_Range i8 =
            { self with Core_models.Ops.Range.f_end = self.Core_models.Ops.Range.f_end -! mk_i8 1 }
            <:
            Core_models.Ops.Range.t_Range i8
          in
          self,
          (Core_models.Option.Option_Some self.Core_models.Ops.Range.f_end
            <:
            Core_models.Option.t_Option i8)
          <:
          (Core_models.Ops.Range.t_Range i8 & Core_models.Option.t_Option i8)
      in
      self, hax_temp_output <: (Core_models.Ops.Range.t_Range i8 & Core_models.Option.t_Option i8)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9: Core_models.Iter.Traits.Double_ended.t_DoubleEndedIterator
(Core_models.Ops.Range.t_Range i16) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_next_back_pre = (fun (self: Core_models.Ops.Range.t_Range i16) -> true);
    f_next_back_post
    =
    (fun
        (self: Core_models.Ops.Range.t_Range i16)
        (out: (Core_models.Ops.Range.t_Range i16 & Core_models.Option.t_Option i16))
        ->
        true);
    f_next_back
    =
    fun (self: Core_models.Ops.Range.t_Range i16) ->
      let
      (self: Core_models.Ops.Range.t_Range i16), (hax_temp_output: Core_models.Option.t_Option i16)
      =
        if self.Core_models.Ops.Range.f_start >=. self.Core_models.Ops.Range.f_end
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option i16)
          <:
          (Core_models.Ops.Range.t_Range i16 & Core_models.Option.t_Option i16)
        else
          let self:Core_models.Ops.Range.t_Range i16 =
            { self with Core_models.Ops.Range.f_end = self.Core_models.Ops.Range.f_end -! mk_i16 1 }
            <:
            Core_models.Ops.Range.t_Range i16
          in
          self,
          (Core_models.Option.Option_Some self.Core_models.Ops.Range.f_end
            <:
            Core_models.Option.t_Option i16)
          <:
          (Core_models.Ops.Range.t_Range i16 & Core_models.Option.t_Option i16)
      in
      self, hax_temp_output <: (Core_models.Ops.Range.t_Range i16 & Core_models.Option.t_Option i16)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10: Core_models.Iter.Traits.Double_ended.t_DoubleEndedIterator
(Core_models.Ops.Range.t_Range i32) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_next_back_pre = (fun (self: Core_models.Ops.Range.t_Range i32) -> true);
    f_next_back_post
    =
    (fun
        (self: Core_models.Ops.Range.t_Range i32)
        (out: (Core_models.Ops.Range.t_Range i32 & Core_models.Option.t_Option i32))
        ->
        true);
    f_next_back
    =
    fun (self: Core_models.Ops.Range.t_Range i32) ->
      let
      (self: Core_models.Ops.Range.t_Range i32), (hax_temp_output: Core_models.Option.t_Option i32)
      =
        if self.Core_models.Ops.Range.f_start >=. self.Core_models.Ops.Range.f_end
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option i32)
          <:
          (Core_models.Ops.Range.t_Range i32 & Core_models.Option.t_Option i32)
        else
          let self:Core_models.Ops.Range.t_Range i32 =
            { self with Core_models.Ops.Range.f_end = self.Core_models.Ops.Range.f_end -! mk_i32 1 }
            <:
            Core_models.Ops.Range.t_Range i32
          in
          self,
          (Core_models.Option.Option_Some self.Core_models.Ops.Range.f_end
            <:
            Core_models.Option.t_Option i32)
          <:
          (Core_models.Ops.Range.t_Range i32 & Core_models.Option.t_Option i32)
      in
      self, hax_temp_output <: (Core_models.Ops.Range.t_Range i32 & Core_models.Option.t_Option i32)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_11: Core_models.Iter.Traits.Double_ended.t_DoubleEndedIterator
(Core_models.Ops.Range.t_Range i64) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_next_back_pre = (fun (self: Core_models.Ops.Range.t_Range i64) -> true);
    f_next_back_post
    =
    (fun
        (self: Core_models.Ops.Range.t_Range i64)
        (out: (Core_models.Ops.Range.t_Range i64 & Core_models.Option.t_Option i64))
        ->
        true);
    f_next_back
    =
    fun (self: Core_models.Ops.Range.t_Range i64) ->
      let
      (self: Core_models.Ops.Range.t_Range i64), (hax_temp_output: Core_models.Option.t_Option i64)
      =
        if self.Core_models.Ops.Range.f_start >=. self.Core_models.Ops.Range.f_end
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option i64)
          <:
          (Core_models.Ops.Range.t_Range i64 & Core_models.Option.t_Option i64)
        else
          let self:Core_models.Ops.Range.t_Range i64 =
            { self with Core_models.Ops.Range.f_end = self.Core_models.Ops.Range.f_end -! mk_i64 1 }
            <:
            Core_models.Ops.Range.t_Range i64
          in
          self,
          (Core_models.Option.Option_Some self.Core_models.Ops.Range.f_end
            <:
            Core_models.Option.t_Option i64)
          <:
          (Core_models.Ops.Range.t_Range i64 & Core_models.Option.t_Option i64)
      in
      self, hax_temp_output <: (Core_models.Ops.Range.t_Range i64 & Core_models.Option.t_Option i64)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_12: Core_models.Iter.Traits.Double_ended.t_DoubleEndedIterator
(Core_models.Ops.Range.t_Range i128) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_next_back_pre = (fun (self: Core_models.Ops.Range.t_Range i128) -> true);
    f_next_back_post
    =
    (fun
        (self: Core_models.Ops.Range.t_Range i128)
        (out: (Core_models.Ops.Range.t_Range i128 & Core_models.Option.t_Option i128))
        ->
        true);
    f_next_back
    =
    fun (self: Core_models.Ops.Range.t_Range i128) ->
      let
      (self: Core_models.Ops.Range.t_Range i128),
      (hax_temp_output: Core_models.Option.t_Option i128) =
        if self.Core_models.Ops.Range.f_start >=. self.Core_models.Ops.Range.f_end
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option i128)
          <:
          (Core_models.Ops.Range.t_Range i128 & Core_models.Option.t_Option i128)
        else
          let self:Core_models.Ops.Range.t_Range i128 =
            {
              self with
              Core_models.Ops.Range.f_end = self.Core_models.Ops.Range.f_end -! mk_i128 1
            }
            <:
            Core_models.Ops.Range.t_Range i128
          in
          self,
          (Core_models.Option.Option_Some self.Core_models.Ops.Range.f_end
            <:
            Core_models.Option.t_Option i128)
          <:
          (Core_models.Ops.Range.t_Range i128 & Core_models.Option.t_Option i128)
      in
      self, hax_temp_output
      <:
      (Core_models.Ops.Range.t_Range i128 & Core_models.Option.t_Option i128)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_13: Core_models.Iter.Traits.Double_ended.t_DoubleEndedIterator
(Core_models.Ops.Range.t_Range isize) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_next_back_pre = (fun (self: Core_models.Ops.Range.t_Range isize) -> true);
    f_next_back_post
    =
    (fun
        (self: Core_models.Ops.Range.t_Range isize)
        (out: (Core_models.Ops.Range.t_Range isize & Core_models.Option.t_Option isize))
        ->
        true);
    f_next_back
    =
    fun (self: Core_models.Ops.Range.t_Range isize) ->
      let
      (self: Core_models.Ops.Range.t_Range isize),
      (hax_temp_output: Core_models.Option.t_Option isize) =
        if self.Core_models.Ops.Range.f_start >=. self.Core_models.Ops.Range.f_end
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option isize)
          <:
          (Core_models.Ops.Range.t_Range isize & Core_models.Option.t_Option isize)
        else
          let self:Core_models.Ops.Range.t_Range isize =
            {
              self with
              Core_models.Ops.Range.f_end = self.Core_models.Ops.Range.f_end -! mk_isize 1
            }
            <:
            Core_models.Ops.Range.t_Range isize
          in
          self,
          (Core_models.Option.Option_Some self.Core_models.Ops.Range.f_end
            <:
            Core_models.Option.t_Option isize)
          <:
          (Core_models.Ops.Range.t_Range isize & Core_models.Option.t_Option isize)
      in
      self, hax_temp_output
      <:
      (Core_models.Ops.Range.t_Range isize & Core_models.Option.t_Option isize)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_14: Core_models.Iter.Traits.Exact_size.t_ExactSizeIterator
(Core_models.Ops.Range.t_Range u8) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_len_pre = (fun (self: Core_models.Ops.Range.t_Range u8) -> true);
    f_len_post = (fun (self: Core_models.Ops.Range.t_Range u8) (out: usize) -> true);
    f_len
    =
    fun (self: Core_models.Ops.Range.t_Range u8) ->
      if self.Core_models.Ops.Range.f_start >=. self.Core_models.Ops.Range.f_end
      then mk_usize 0
      else
        cast (self.Core_models.Ops.Range.f_end -! self.Core_models.Ops.Range.f_start <: u8) <: usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_15: Core_models.Iter.Traits.Exact_size.t_ExactSizeIterator
(Core_models.Ops.Range.t_Range u16) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_len_pre = (fun (self: Core_models.Ops.Range.t_Range u16) -> true);
    f_len_post = (fun (self: Core_models.Ops.Range.t_Range u16) (out: usize) -> true);
    f_len
    =
    fun (self: Core_models.Ops.Range.t_Range u16) ->
      if self.Core_models.Ops.Range.f_start >=. self.Core_models.Ops.Range.f_end
      then mk_usize 0
      else
        cast (self.Core_models.Ops.Range.f_end -! self.Core_models.Ops.Range.f_start <: u16)
        <:
        usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_16: Core_models.Iter.Traits.Exact_size.t_ExactSizeIterator
(Core_models.Ops.Range.t_Range u32) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_len_pre = (fun (self: Core_models.Ops.Range.t_Range u32) -> true);
    f_len_post = (fun (self: Core_models.Ops.Range.t_Range u32) (out: usize) -> true);
    f_len
    =
    fun (self: Core_models.Ops.Range.t_Range u32) ->
      if self.Core_models.Ops.Range.f_start >=. self.Core_models.Ops.Range.f_end
      then mk_usize 0
      else
        cast (self.Core_models.Ops.Range.f_end -! self.Core_models.Ops.Range.f_start <: u32)
        <:
        usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_17: Core_models.Iter.Traits.Exact_size.t_ExactSizeIterator
(Core_models.Ops.Range.t_Range usize) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_len_pre = (fun (self: Core_models.Ops.Range.t_Range usize) -> true);
    f_len_post = (fun (self: Core_models.Ops.Range.t_Range usize) (out: usize) -> true);
    f_len
    =
    fun (self: Core_models.Ops.Range.t_Range usize) ->
      if self.Core_models.Ops.Range.f_start >=. self.Core_models.Ops.Range.f_end
      then mk_usize 0
      else self.Core_models.Ops.Range.f_end -! self.Core_models.Ops.Range.f_start
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_18: Core_models.Iter.Traits.Exact_size.t_ExactSizeIterator
(Core_models.Ops.Range.t_Range i8) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_len_pre = (fun (self: Core_models.Ops.Range.t_Range i8) -> true);
    f_len_post = (fun (self: Core_models.Ops.Range.t_Range i8) (out: usize) -> true);
    f_len
    =
    fun (self: Core_models.Ops.Range.t_Range i8) ->
      if self.Core_models.Ops.Range.f_start >=. self.Core_models.Ops.Range.f_end
      then mk_usize 0
      else
        cast (Core_models.Num.impl_isize__wrapping_sub (cast (self.Core_models.Ops.Range.f_end <: i8
                  )
                <:
                isize)
              (cast (self.Core_models.Ops.Range.f_start <: i8) <: isize)
            <:
            isize)
        <:
        usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_19: Core_models.Iter.Traits.Exact_size.t_ExactSizeIterator
(Core_models.Ops.Range.t_Range i16) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_len_pre = (fun (self: Core_models.Ops.Range.t_Range i16) -> true);
    f_len_post = (fun (self: Core_models.Ops.Range.t_Range i16) (out: usize) -> true);
    f_len
    =
    fun (self: Core_models.Ops.Range.t_Range i16) ->
      if self.Core_models.Ops.Range.f_start >=. self.Core_models.Ops.Range.f_end
      then mk_usize 0
      else
        cast (Core_models.Num.impl_isize__wrapping_sub (cast (self.Core_models.Ops.Range.f_end
                    <:
                    i16)
                <:
                isize)
              (cast (self.Core_models.Ops.Range.f_start <: i16) <: isize)
            <:
            isize)
        <:
        usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_20: Core_models.Iter.Traits.Exact_size.t_ExactSizeIterator
(Core_models.Ops.Range.t_Range i32) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_len_pre = (fun (self: Core_models.Ops.Range.t_Range i32) -> true);
    f_len_post = (fun (self: Core_models.Ops.Range.t_Range i32) (out: usize) -> true);
    f_len
    =
    fun (self: Core_models.Ops.Range.t_Range i32) ->
      if self.Core_models.Ops.Range.f_start >=. self.Core_models.Ops.Range.f_end
      then mk_usize 0
      else
        cast (Core_models.Num.impl_isize__wrapping_sub (cast (self.Core_models.Ops.Range.f_end
                    <:
                    i32)
                <:
                isize)
              (cast (self.Core_models.Ops.Range.f_start <: i32) <: isize)
            <:
            isize)
        <:
        usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_21: Core_models.Iter.Traits.Exact_size.t_ExactSizeIterator
(Core_models.Ops.Range.t_Range isize) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_len_pre = (fun (self: Core_models.Ops.Range.t_Range isize) -> true);
    f_len_post = (fun (self: Core_models.Ops.Range.t_Range isize) (out: usize) -> true);
    f_len
    =
    fun (self: Core_models.Ops.Range.t_Range isize) ->
      if self.Core_models.Ops.Range.f_start >=. self.Core_models.Ops.Range.f_end
      then mk_usize 0
      else
        cast (Core_models.Num.impl_isize__wrapping_sub self.Core_models.Ops.Range.f_end
              self.Core_models.Ops.Range.f_start
            <:
            isize)
        <:
        usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_T: Type0)
    : Core_models.Iter.Traits.Double_ended.t_DoubleEndedIterator (Core_models.Slice.Iter.t_Iter v_T) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_next_back_pre = (fun (self: Core_models.Slice.Iter.t_Iter v_T) -> true);
    f_next_back_post
    =
    (fun
        (self: Core_models.Slice.Iter.t_Iter v_T)
        (out1: (Core_models.Slice.Iter.t_Iter v_T & Core_models.Option.t_Option v_T))
        ->
        true);
    f_next_back
    =
    fun (self: Core_models.Slice.Iter.t_Iter v_T) ->
      let n:usize = Rust_primitives.Sequence.seq_len #v_T self.Core_models.Slice.Iter._0 in
      let
      (self: Core_models.Slice.Iter.t_Iter v_T), (hax_temp_output: Core_models.Option.t_Option v_T)
      =
        if n =. mk_usize 0
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_T)
          <:
          (Core_models.Slice.Iter.t_Iter v_T & Core_models.Option.t_Option v_T)
        else
          let (tmp0: Rust_primitives.Sequence.t_Seq v_T), (out: v_T) =
            Rust_primitives.Sequence.seq_remove #v_T
              self.Core_models.Slice.Iter._0
              (n -! mk_usize 1 <: usize)
          in
          let self:Core_models.Slice.Iter.t_Iter v_T =
            { self with Core_models.Slice.Iter._0 = tmp0 } <: Core_models.Slice.Iter.t_Iter v_T
          in
          self, (Core_models.Option.Option_Some out <: Core_models.Option.t_Option v_T)
          <:
          (Core_models.Slice.Iter.t_Iter v_T & Core_models.Option.t_Option v_T)
      in
      self, hax_temp_output <: (Core_models.Slice.Iter.t_Iter v_T & Core_models.Option.t_Option v_T)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1 (#v_T: Type0)
    : Core_models.Iter.Traits.Exact_size.t_ExactSizeIterator (Core_models.Slice.Iter.t_Iter v_T) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_len_pre = (fun (self: Core_models.Slice.Iter.t_Iter v_T) -> true);
    f_len_post = (fun (self: Core_models.Slice.Iter.t_Iter v_T) (out: usize) -> true);
    f_len
    =
    fun (self: Core_models.Slice.Iter.t_Iter v_T) ->
      Rust_primitives.Sequence.seq_len #v_T self.Core_models.Slice.Iter._0
  }
