module Core_models.Iter.Ends
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': Core_models.Iter.Traits.Double_ended.t_DoubleEndedIterator
(Core_models.Ops.Range.t_Range u8)

unfold
let impl_1 = impl_1'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2': Core_models.Iter.Traits.Double_ended.t_DoubleEndedIterator
(Core_models.Ops.Range.t_Range u16)

unfold
let impl_2 = impl_2'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': Core_models.Iter.Traits.Double_ended.t_DoubleEndedIterator
(Core_models.Ops.Range.t_Range u32)

unfold
let impl_3 = impl_3'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_4': Core_models.Iter.Traits.Double_ended.t_DoubleEndedIterator
(Core_models.Ops.Range.t_Range u64)

unfold
let impl_4 = impl_4'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_5': Core_models.Iter.Traits.Double_ended.t_DoubleEndedIterator
(Core_models.Ops.Range.t_Range u128)

unfold
let impl_5 = impl_5'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_6': Core_models.Iter.Traits.Double_ended.t_DoubleEndedIterator
(Core_models.Ops.Range.t_Range usize)

unfold
let impl_6 = impl_6'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_7': Core_models.Iter.Traits.Double_ended.t_DoubleEndedIterator
(Core_models.Ops.Range.t_Range i8)

unfold
let impl_7 = impl_7'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_8': Core_models.Iter.Traits.Double_ended.t_DoubleEndedIterator
(Core_models.Ops.Range.t_Range i16)

unfold
let impl_8 = impl_8'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_9': Core_models.Iter.Traits.Double_ended.t_DoubleEndedIterator
(Core_models.Ops.Range.t_Range i32)

unfold
let impl_9 = impl_9'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_10': Core_models.Iter.Traits.Double_ended.t_DoubleEndedIterator
(Core_models.Ops.Range.t_Range i64)

unfold
let impl_10 = impl_10'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_11': Core_models.Iter.Traits.Double_ended.t_DoubleEndedIterator
(Core_models.Ops.Range.t_Range i128)

unfold
let impl_11 = impl_11'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_12': Core_models.Iter.Traits.Double_ended.t_DoubleEndedIterator
(Core_models.Ops.Range.t_Range isize)

unfold
let impl_12 = impl_12'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_13: Core_models.Iter.Traits.Exact_size.t_ExactSizeIterator
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
let impl_14: Core_models.Iter.Traits.Exact_size.t_ExactSizeIterator
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
let impl_15: Core_models.Iter.Traits.Exact_size.t_ExactSizeIterator
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
let impl_16: Core_models.Iter.Traits.Exact_size.t_ExactSizeIterator
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
let impl_17: Core_models.Iter.Traits.Exact_size.t_ExactSizeIterator
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
let impl_18: Core_models.Iter.Traits.Exact_size.t_ExactSizeIterator
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
let impl_19: Core_models.Iter.Traits.Exact_size.t_ExactSizeIterator
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
let impl_20: Core_models.Iter.Traits.Exact_size.t_ExactSizeIterator
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
assume
val impl_21': #v_T: Type0
  -> Core_models.Iter.Traits.Double_ended.t_DoubleEndedIterator (Core_models.Slice.Iter.t_Iter v_T)

unfold
let impl_21 (#v_T: Type0) = impl_21' #v_T

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_T: Type0)
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
