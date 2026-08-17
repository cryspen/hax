module Core_models.Bundle
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::array::TryFromSliceError`]
type t_TryFromSliceError = | TryFromSliceError : t_TryFromSliceError

let impl_23__map
      (#v_T: Type0)
      (v_N: usize)
      (#v_F #v_U: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_T)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_U})
      (s: t_Array v_T v_N)
      (f: (v_T -> v_U))
    : t_Array v_U v_N = Rust_primitives.Slice.array_map #v_T #v_U v_N #(v_T -> v_U) s f

/// See [`std::array::as_slice`]
let impl_23__as_slice (#v_T: Type0) (v_N: usize) (s: t_Array v_T v_N) : t_Slice v_T =
  Rust_primitives.Slice.array_as_slice #v_T v_N s

/// See [`std::array::each_ref`]
let impl_23__each_ref (#v_T: Type0) (v_N: usize) (s: t_Array v_T v_N) : t_Array v_T v_N =
  Rust_primitives.Slice.array_from_fn #v_T
    v_N
    #(usize -> v_T)
    (fun i ->
        let i:usize = i in
        Rust_primitives.Slice.array_index #v_T v_N s i <: v_T)

let from_fn = Rust_primitives.Slice.array_from_fn

/// See [`std::array::from_ref`]
let from_ref (#v_T: Type0) (s: v_T) : t_Array v_T (mk_usize 1) =
  Rust_primitives.Slice.array_from_ref #v_T s

/// See [`std::array::repeat`]
let repeat
      (#v_T: Type0)
      (v_N: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Clone.t_Clone v_T)
      (v_val: v_T)
    : t_Array v_T v_N = Rust_primitives.Slice.array_repeat #v_T v_N v_val

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_25 (#v_T: Type0) (v_N: usize) : Core_models.Ops.Index.t_Index (t_Array v_T v_N) usize =
  {
    f_Output = v_T;
    f_index_pre = (fun (self_: t_Array v_T v_N) (i: usize) -> i <. v_N);
    f_index_post = (fun (self: t_Array v_T v_N) (i: usize) (out: v_T) -> true);
    f_index
    =
    fun (self: t_Array v_T v_N) (i: usize) -> Rust_primitives.Slice.array_index #v_T v_N self i
  }

/// The elements not yet yielded, in order.
type t_IntoIter (v_T: Type0) (v_N: usize) =
  | IntoIter : Rust_primitives.Sequence.t_Seq v_T -> t_IntoIter v_T v_N

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_24 (#v_T: Type0) (v_N: usize)
    : Core_models.Iter.Traits.Collect.t_IntoIterator (t_Array v_T v_N) =
  {
    f_Item = v_T;
    f_IntoIter = t_IntoIter v_T v_N;
    f_into_iter_pre = (fun (self: t_Array v_T v_N) -> true);
    f_into_iter_post = (fun (self: t_Array v_T v_N) (out: t_IntoIter v_T v_N) -> true);
    f_into_iter
    =
    fun (self: t_Array v_T v_N) ->
      IntoIter (Rust_primitives.Sequence.seq_from_array #v_T v_N self) <: t_IntoIter v_T v_N
  }

/// See [`std::array::IntoIter::new`]
let impl_1__new (#v_T: Type0) (v_N: usize) (arr: t_Array v_T v_N) : t_IntoIter v_T v_N =
  IntoIter (Rust_primitives.Sequence.seq_from_array #v_T v_N arr) <: t_IntoIter v_T v_N

/// See [`std::array::IntoIter::empty`]
let impl_1__empty (#v_T: Type0) (v_N: usize) (_: Prims.unit) : t_IntoIter v_T v_N =
  IntoIter (Rust_primitives.Sequence.seq_empty #v_T ()) <: t_IntoIter v_T v_N

/// See [`std::array::IntoIter::as_slice`]
let impl_1__as_slice (#v_T: Type0) (v_N: usize) (self: t_IntoIter v_T v_N) : t_Slice v_T =
  Rust_primitives.Sequence.seq_to_slice #v_T self._0

/// See [`std::cmp::Ordering`]
type t_Ordering =
  | Ordering_Less : t_Ordering
  | Ordering_Equal : t_Ordering
  | Ordering_Greater : t_Ordering

let anon_const_Ordering_Less__anon_const_0: isize = mk_isize (-1)

let anon_const_Ordering_Equal__anon_const_0: isize = mk_isize 0

let anon_const_Ordering_Greater__anon_const_0: isize = mk_isize 1

let t_Ordering_cast_to_repr (x: t_Ordering) : isize =
  match x <: t_Ordering with
  | Ordering_Less  -> anon_const_Ordering_Less__anon_const_0
  | Ordering_Equal  -> anon_const_Ordering_Equal__anon_const_0
  | Ordering_Greater  -> anon_const_Ordering_Greater__anon_const_0

/// See [`std::cmp::Reverse`]
type t_Reverse (v_T: Type0) = | Reverse : v_T -> t_Reverse v_T

/// See [`std::cmp::Ordering::is_eq`]
let impl_54__is_eq (self: t_Ordering) : bool =
  match self <: t_Ordering with
  | Ordering_Equal  -> true
  | _ -> false

/// See [`std::cmp::Ordering::is_ne`]
let impl_54__is_ne (self: t_Ordering) : bool =
  match self <: t_Ordering with
  | Ordering_Less  | Ordering_Greater  -> true
  | _ -> false

/// See [`std::cmp::Ordering::is_lt`]
let impl_54__is_lt (self: t_Ordering) : bool =
  match self <: t_Ordering with
  | Ordering_Less  -> true
  | _ -> false

/// See [`std::cmp::Ordering::is_gt`]
let impl_54__is_gt (self: t_Ordering) : bool =
  match self <: t_Ordering with
  | Ordering_Greater  -> true
  | _ -> false

/// See [`std::cmp::Ordering::is_le`]
let impl_54__is_le (self: t_Ordering) : bool =
  match self <: t_Ordering with
  | Ordering_Less  | Ordering_Equal  -> true
  | _ -> false

/// See [`std::cmp::Ordering::is_ge`]
let impl_54__is_ge (self: t_Ordering) : bool =
  match self <: t_Ordering with
  | Ordering_Greater  | Ordering_Equal  -> true
  | _ -> false

/// See [`std::cmp::Ordering::reverse`]
let impl_54__reverse (self: t_Ordering) : t_Ordering =
  match self <: t_Ordering with
  | Ordering_Less  -> Ordering_Greater <: t_Ordering
  | Ordering_Equal  -> Ordering_Equal <: t_Ordering
  | Ordering_Greater  -> Ordering_Less <: t_Ordering

/// See [`std::cmp::Ordering::then`]
let impl_54__then (self other: t_Ordering) : t_Ordering =
  match self <: t_Ordering with
  | Ordering_Equal  -> other
  | _ -> self

/// See [`std::cmp::Ordering::then_with`]
let impl_54__then_with
      (#v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Core_models.Ops.Function.t_FnOnce v_F Prims.unit)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == t_Ordering})
      (self: t_Ordering)
      (f: v_F)
    : t_Ordering =
  match self <: t_Ordering with
  | Ordering_Equal  ->
    Core_models.Ops.Function.f_call_once #v_F
      #Prims.unit
      #FStar.Tactics.Typeclasses.solve
      f
      (() <: Prims.unit)
  | _ -> self

/// See [`std::cmp::max_by`]
let max_by
      (#v_T #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Core_models.Ops.Function.t_FnOnce v_F (v_T & v_T))
      (#_: unit{i0.Core_models.Ops.Function.f_Output == t_Ordering})
      (v1 v2: v_T)
      (compare: v_F)
    : v_T =
  if
    impl_54__is_lt (Core_models.Ops.Function.f_call_once #v_F
          #(v_T & v_T)
          #FStar.Tactics.Typeclasses.solve
          compare
          (v2, v1 <: (v_T & v_T))
        <:
        t_Ordering)
  then v1
  else v2

/// See [`std::cmp::min_by`]
let min_by
      (#v_T #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Core_models.Ops.Function.t_FnOnce v_F (v_T & v_T))
      (#_: unit{i0.Core_models.Ops.Function.f_Output == t_Ordering})
      (v1 v2: v_T)
      (compare: v_F)
    : v_T =
  if
    impl_54__is_lt (Core_models.Ops.Function.f_call_once #v_F
          #(v_T & v_T)
          #FStar.Tactics.Typeclasses.solve
          compare
          (v2, v1 <: (v_T & v_T))
        <:
        t_Ordering)
  then v2
  else v1

/// See [`std::cmp::minmax_by`]
let minmax_by
      (#v_T #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Core_models.Ops.Function.t_FnOnce v_F (v_T & v_T))
      (#_: unit{i0.Core_models.Ops.Function.f_Output == t_Ordering})
      (v1 v2: v_T)
      (compare: v_F)
    : t_Array v_T (mk_usize 2) =
  if
    impl_54__is_lt (Core_models.Ops.Function.f_call_once #v_F
          #(v_T & v_T)
          #FStar.Tactics.Typeclasses.solve
          compare
          (v2, v1 <: (v_T & v_T))
        <:
        t_Ordering)
  then Rust_primitives.Slice.array_pair #v_T v2 v1
  else Rust_primitives.Slice.array_pair #v_T v1 v2

/// See [`std::convert::Infallible`]
type t_Infallible = | Infallible : t_Infallible

/// See [`std::convert::identity`]
let identity (#v_T: Type0) (x: v_T) : v_T = x

/// See [`std::iter::Enumerate`]
type t_Enumerate (v_I: Type0) = {
  f_iter:v_I;
  f_count:usize
}

let impl__new (#v_I: Type0) (iter: v_I) : t_Enumerate v_I =
  { f_iter = iter; f_count = mk_usize 0 } <: t_Enumerate v_I

/// See [`std::iter::Filter`]
type t_Filter (v_I: Type0) (v_P: Type0) = {
  f_iter:v_I;
  f_predicate:v_P
}

let impl__new__from__filter (#v_I #v_P: Type0) (iter: v_I) (predicate: v_P) : t_Filter v_I v_P =
  { f_iter = iter; f_predicate = predicate } <: t_Filter v_I v_P

/// See [`std::iter::Map`]
type t_Map (v_I: Type0) (v_F: Type0) = {
  f_iter:v_I;
  f_f:v_F
}

let impl__new__from__map (#v_I #v_F: Type0) (iter: v_I) (f: v_F) : t_Map v_I v_F =
  { f_iter = iter; f_f = f } <: t_Map v_I v_F

/// See [`std::iter::Skip`]
type t_Skip (v_I: Type0) = {
  f_iter:v_I;
  f_n:usize
}

let impl__new__from__skip (#v_I: Type0) (iter: v_I) (n: usize) : t_Skip v_I =
  { f_iter = iter; f_n = n } <: t_Skip v_I

/// See [`std::iter::StepBy`]
type t_StepBy (v_I: Type0) = {
  f_iter:v_I;
  f_step:usize
}

let impl__new__from__step_by (#v_I: Type0) (iter: v_I) (step: usize)
    : Prims.Pure (t_StepBy v_I) (requires step >. mk_usize 0) (fun _ -> Prims.l_True) =
  let _:Prims.unit =
    if step =. mk_usize 0 then Core_models.Panicking.Internal.panic #Prims.unit ()
  in
  { f_iter = iter; f_step = step } <: t_StepBy v_I

/// See [`std::iter::Take`]
type t_Take (v_I: Type0) = {
  f_iter:v_I;
  f_n:usize
}

let impl__new__from__take (#v_I: Type0) (iter: v_I) (n: usize) : t_Take v_I =
  { f_iter = iter; f_n = n } <: t_Take v_I

/// See [`std::iter::Zip`]
type t_Zip (v_I1: Type0) (v_I2: Type0) = {
  f_it1:v_I1;
  f_it2:v_I2
}

/// See [`std::primitive::u8::MIN`] (and similar for other unsigned integer types)
let impl_6__MIN: u8 = mk_u8 0

/// See [`std::primitive::u8::MAX`] (and similar for other unsigned integer types)
let impl_6__MAX: u8 = mk_u8 255

/// See [`std::primitive::u8::BITS`] (and similar for other unsigned integer types)
let impl_6__BITS: u32 = mk_u32 8

/// See [`std::primitive::u8::wrapping_add`] (and similar for other unsigned integer types)
let impl_6__wrapping_add (x y: u8) : u8 = Rust_primitives.Arithmetic.wrapping_add_u8 x y

/// See [`std::primitive::u8::saturating_add`] (and similar for other integer types)
let impl_6__saturating_add (x y: u8) : u8 = Rust_primitives.Arithmetic.saturating_add_u8 x y

/// See [`std::primitive::u8::overflowing_add`] (and similar for other integer types)
let impl_6__overflowing_add (x y: u8) : (u8 & bool) =
  Rust_primitives.Arithmetic.overflowing_add_u8 x y

/// See [`std::primitive::u8::wrapping_sub`] (and similar for other integer types)
let impl_6__wrapping_sub (x y: u8) : u8 = Rust_primitives.Arithmetic.wrapping_sub_u8 x y

/// See [`std::primitive::u8::saturating_sub`] (and similar for other integer types)
let impl_6__saturating_sub (x y: u8) : u8 = Rust_primitives.Arithmetic.saturating_sub_u8 x y

/// See [`std::primitive::u8::overflowing_sub`] (and similar for other integer types)
let impl_6__overflowing_sub (x y: u8) : (u8 & bool) =
  Rust_primitives.Arithmetic.overflowing_sub_u8 x y

/// See [`std::primitive::u8::wrapping_mul`] (and similar for other integer types)
let impl_6__wrapping_mul (x y: u8) : u8 = Rust_primitives.Arithmetic.wrapping_mul_u8 x y

/// See [`std::primitive::u8::saturating_mul`] (and similar for other integer types)
let impl_6__saturating_mul (x y: u8) : u8 = Rust_primitives.Arithmetic.saturating_mul_u8 x y

/// See [`std::primitive::u8::overflowing_mul`] (and similar for other integer types)
let impl_6__overflowing_mul (x y: u8) : (u8 & bool) =
  Rust_primitives.Arithmetic.overflowing_mul_u8 x y

/// See [`std::primitive::u8::pow`] (and similar for other integer types)
let impl_6__pow (x: u8) (exp: u32) : u8 = Rust_primitives.Arithmetic.pow_u8 x exp

/// See [`std::primitive::u8::overflowing_pow`] (and similar for other integer types)
let impl_6__overflowing_pow (x: u8) (exp: u32) : (u8 & bool) =
  Rust_primitives.Arithmetic.overflowing_pow_u8 x exp

/// See [`std::primitive::u8::count_ones`] (and similar for other integer types)
let impl_6__count_ones (x: u8) : u32 = Rust_primitives.Arithmetic.count_ones_u8 x

/// See [`std::primitive::u8::rotate_right`] (and similar for other integer types)
assume
val impl_6__rotate_right': x: u8 -> n: u32 -> u8

unfold
let impl_6__rotate_right = impl_6__rotate_right'

/// See [`std::primitive::u8::rotate_left`] (and similar for other integer types)
assume
val impl_6__rotate_left': x: u8 -> n: u32 -> u8

unfold
let impl_6__rotate_left = impl_6__rotate_left'

/// See [`std::primitive::u8::leading_zeros`] (and similar for other integer types)
assume
val impl_6__leading_zeros': x: u8 -> u32

unfold
let impl_6__leading_zeros = impl_6__leading_zeros'

/// See [`std::primitive::u8::ilog2`] (and similar for other integer types)
assume
val impl_6__ilog2': x: u8 -> u32

unfold
let impl_6__ilog2 = impl_6__ilog2'

/// See [`std::primitive::u8::from_be_bytes`] (and similar for other integer types)
assume
val impl_6__from_be_bytes': bytes: t_Array u8 (mk_usize 1) -> u8

unfold
let impl_6__from_be_bytes = impl_6__from_be_bytes'

/// See [`std::primitive::u8::from_le_bytes`] (and similar for other integer types)
assume
val impl_6__from_le_bytes': bytes: t_Array u8 (mk_usize 1) -> u8

unfold
let impl_6__from_le_bytes = impl_6__from_le_bytes'

/// See [`std::primitive::u8::to_be_bytes`] (and similar for other integer types)
assume
val impl_6__to_be_bytes': bytes: u8 -> t_Array u8 (mk_usize 1)

unfold
let impl_6__to_be_bytes = impl_6__to_be_bytes'

/// See [`std::primitive::u8::to_le_bytes`] (and similar for other integer types)
assume
val impl_6__to_le_bytes': bytes: u8 -> t_Array u8 (mk_usize 1)

unfold
let impl_6__to_le_bytes = impl_6__to_le_bytes'

/// See [`std::primitive::u8::is_power_of_two`] (and similar for other unsigned integer types)
let impl_6__is_power_of_two (x: u8) : bool =
  x <>. mk_u8 0 && (x &. (x -! mk_u8 1 <: u8) <: u8) =. mk_u8 0

/// See [`std::primitive::u8::is_multiple_of`] (and similar for other unsigned integer types)
let impl_6__is_multiple_of (x y: u8) : bool =
  if y =. mk_u8 0 then x =. mk_u8 0 else (x %! y <: u8) =. mk_u8 0

/// See [`std::primitive::u8::wrapping_neg`] (and similar for other integer types)
let impl_6__wrapping_neg (x: u8) : u8 = Rust_primitives.Arithmetic.wrapping_sub_u8 (mk_u8 0) x

/// See [`std::primitive::u8::min_value`] (and similar for other integer types)
let impl_6__min_value (_: Prims.unit) : u8 = impl_6__MIN

/// See [`std::primitive::u8::max_value`] (and similar for other integer types)
let impl_6__max_value (_: Prims.unit) : u8 = impl_6__MAX

/// See [`std::primitive::u8::cast_signed`] (and similar for other unsigned integer types)
let impl_6__cast_signed (x: u8) : i8 = cast (x <: u8) <: i8

/// See [`std::primitive::u8::count_zeros`] (and similar for other integer types)
let impl_6__count_zeros (x: u8) : u32 = impl_6__BITS -! (impl_6__count_ones x <: u32)

/// See [`std::primitive::u8::overflowing_neg`] (and similar for other integer types)
let impl_6__overflowing_neg (x: u8) : (u8 & bool) =
  impl_6__wrapping_neg x, x <>. mk_u8 0 <: (u8 & bool)

/// See [`std::primitive::u8::wrapping_pow`] (and similar for other integer types)
let impl_6__wrapping_pow (x: u8) (exp: u32) : u8 =
  let (result: u8), (_: bool) = impl_6__overflowing_pow x exp in
  result

/// See [`std::primitive::u8::saturating_pow`] (and similar for other unsigned integer types)
let impl_6__saturating_pow (x: u8) (exp: u32) : u8 =
  let (result: u8), (overflowed: bool) = impl_6__overflowing_pow x exp in
  if overflowed then impl_6__MAX else result

/// See [`std::primitive::u8::abs_diff`] (and similar for other unsigned integer types)
let impl_6__abs_diff (x y: u8) : u8 = if x <. y then y -! x else x -! y

/// See [`std::primitive::u8::midpoint`] (and similar for other unsigned integer types)
let impl_6__midpoint (x y: u8) : u8 =
  impl_6__wrapping_add ((x ^. y <: u8) >>! mk_i32 1 <: u8) (x &. y <: u8)

/// See [`std::primitive::u8::wrapping_add_signed`] (and similar for other unsigned integer types)
let impl_6__wrapping_add_signed (x: u8) (y: i8) : u8 = impl_6__wrapping_add x (cast (y <: i8) <: u8)

/// See [`std::primitive::u8::wrapping_sub_signed`] (and similar for other unsigned integer types)
let impl_6__wrapping_sub_signed (x: u8) (y: i8) : u8 = impl_6__wrapping_sub x (cast (y <: i8) <: u8)

/// See [`std::primitive::u8::overflowing_add_signed`] (and similar for other unsigned integer types)
let impl_6__overflowing_add_signed (x: u8) (y: i8) : (u8 & bool) =
  let (result: u8), (overflowed: bool) = impl_6__overflowing_add x (cast (y <: i8) <: u8) in
  result, overflowed <>. (y <. mk_i8 0 <: bool) <: (u8 & bool)

/// See [`std::primitive::u8::overflowing_sub_signed`] (and similar for other unsigned integer types)
let impl_6__overflowing_sub_signed (x: u8) (y: i8) : (u8 & bool) =
  let (result: u8), (overflowed: bool) = impl_6__overflowing_sub x (cast (y <: i8) <: u8) in
  result, overflowed <>. (y <. mk_i8 0 <: bool) <: (u8 & bool)

/// See [`std::primitive::u8::saturating_add_signed`] (and similar for other unsigned integer types)
let impl_6__saturating_add_signed (x: u8) (y: i8) : u8 =
  let (result: u8), (overflowed: bool) = impl_6__overflowing_add_signed x y in
  if ~.overflowed then result else if y <. mk_i8 0 then impl_6__MIN else impl_6__MAX

/// See [`std::primitive::u8::saturating_sub_signed`] (and similar for other unsigned integer types)
let impl_6__saturating_sub_signed (x: u8) (y: i8) : u8 =
  let (result: u8), (overflowed: bool) = impl_6__overflowing_sub_signed x y in
  if ~.overflowed then result else if y <. mk_i8 0 then impl_6__MAX else impl_6__MIN

/// See [`std::primitive::u8::trailing_zeros`] (and similar for other integer types)
let impl_6__trailing_zeros (x: u8) : u32 =
  if x =. mk_u8 0
  then impl_6__BITS
  else
    impl_6__count_ones (impl_6__wrapping_sub (x &. (impl_6__wrapping_neg x <: u8) <: u8) (mk_u8 1)
        <:
        u8)

/// See [`std::primitive::u8::trailing_ones`] (and similar for other integer types)
let impl_6__trailing_ones (x: u8) : u32 =
  impl_6__trailing_zeros (impl_6__wrapping_sub impl_6__MAX x <: u8)

/// See [`std::primitive::u8::leading_ones`] (and similar for other integer types)
let impl_6__leading_ones (x: u8) : u32 =
  impl_6__leading_zeros (impl_6__wrapping_sub impl_6__MAX x <: u8)

/// See [`std::primitive::u8::bit_width`] (and similar for other unsigned integer types)
assume
val impl_6__bit_width': x: u8 -> u32

unfold
let impl_6__bit_width = impl_6__bit_width'

/// See [`std::primitive::u8::isolate_lowest_one`] (and similar for other integer types)
let impl_6__isolate_lowest_one (x: u8) : u8 = x &. (impl_6__wrapping_neg x <: u8)

/// See [`std::primitive::u8::swap_bytes`] (and similar for other integer types)
let impl_6__swap_bytes (x: u8) : u8 =
  impl_6__from_le_bytes (impl_6__to_be_bytes x <: t_Array u8 (mk_usize 1))

/// See [`std::primitive::u8::to_be`] (and similar for other integer types)
let impl_6__to_be (x: u8) : u8 = impl_6__swap_bytes x

/// See [`std::primitive::u8::to_le`] (and similar for other integer types)
let impl_6__to_le (x: u8) : u8 = x

/// See [`std::primitive::u8::from_be`] (and similar for other integer types)
let impl_6__from_be (x: u8) : u8 = impl_6__swap_bytes x

/// See [`std::primitive::u8::from_le`] (and similar for other integer types)
let impl_6__from_le (x: u8) : u8 = x

/// See [`std::primitive::u8::to_ne_bytes`] (and similar for other integer types)
let impl_6__to_ne_bytes (x: u8) : t_Array u8 (mk_usize 1) = impl_6__to_le_bytes x

/// See [`std::primitive::u8::from_ne_bytes`] (and similar for other integer types)
let impl_6__from_ne_bytes (bytes: t_Array u8 (mk_usize 1)) : u8 = impl_6__from_le_bytes bytes

/// See [`std::primitive::u8::wrapping_shl`] (and similar for other integer types)
let impl_6__wrapping_shl (x: u8) (n: u32) : u8 = x <<! (n %! impl_6__BITS <: u32)

/// See [`std::primitive::u8::wrapping_shr`] (and similar for other integer types)
let impl_6__wrapping_shr (x: u8) (n: u32) : u8 = x >>! (n %! impl_6__BITS <: u32)

/// See [`std::primitive::u8::isolate_highest_one`] (and similar for other integer types)
let impl_6__isolate_highest_one (x: u8) : u8 =
  x &.
  (impl_6__wrapping_shr ((impl_6__MAX /! mk_u8 2 <: u8) +! mk_u8 1 <: u8)
      (impl_6__leading_zeros x <: u32)
    <:
    u8)

/// See [`std::primitive::u8::overflowing_shl`] (and similar for other integer types)
let impl_6__overflowing_shl (x: u8) (n: u32) : (u8 & bool) =
  impl_6__wrapping_shl x n, n >=. impl_6__BITS <: (u8 & bool)

/// See [`std::primitive::u8::overflowing_shr`] (and similar for other integer types)
let impl_6__overflowing_shr (x: u8) (n: u32) : (u8 & bool) =
  impl_6__wrapping_shr x n, n >=. impl_6__BITS <: (u8 & bool)

/// See [`std::primitive::u8::unbounded_shl`] (and similar for other integer types)
let impl_6__unbounded_shl (x: u8) (n: u32) : u8 = if n <. impl_6__BITS then x <<! n else mk_u8 0

/// See [`std::primitive::u8::unbounded_shr`] (and similar for other unsigned integer types)
let impl_6__unbounded_shr (x: u8) (n: u32) : u8 = if n <. impl_6__BITS then x >>! n else mk_u8 0

/// See [`std::primitive::u8::wrapping_next_power_of_two`] (and similar for other unsigned integer types)
let impl_6__wrapping_next_power_of_two (x: u8) : u8 =
  if x <=. mk_u8 1
  then mk_u8 1
  else
    impl_6__wrapping_add (impl_6__MAX >>!
        ((impl_6__leading_zeros (x -! mk_u8 1 <: u8) <: u32) %! impl_6__BITS <: u32)
        <:
        u8)
      (mk_u8 1)

/// See [`std::primitive::u8::reverse_bits`] (and similar for other unsigned integer types)
let impl_6__reverse_bits (x: u8) : u8 =
  let m1:u8 = impl_6__MAX /! mk_u8 3 in
  let m2:u8 = impl_6__MAX /! mk_u8 5 in
  let m4:u8 = impl_6__MAX /! mk_u8 17 in
  let x:u8 =
    (impl_6__wrapping_shl (x &. m1 <: u8) (mk_u32 1) <: u8) |.
    ((impl_6__wrapping_shr x (mk_u32 1) <: u8) &. m1 <: u8)
  in
  let x:u8 =
    (impl_6__wrapping_shl (x &. m2 <: u8) (mk_u32 2) <: u8) |.
    ((impl_6__wrapping_shr x (mk_u32 2) <: u8) &. m2 <: u8)
  in
  let x:u8 =
    (impl_6__wrapping_shl (x &. m4 <: u8) (mk_u32 4) <: u8) |.
    ((impl_6__wrapping_shr x (mk_u32 4) <: u8) &. m4 <: u8)
  in
  impl_6__swap_bytes x

/// See [`std::primitive::u8::widening_mul`] (and similar for other unsigned integer types)
let impl_6__widening_mul (x y: u8) : (u8 & u8) =
  let half:u32 = impl_6__BITS /! mk_u32 2 in
  let lo_mask:u8 = impl_6__wrapping_shr impl_6__MAX half in
  let xl:u8 = x &. lo_mask in
  let xh:u8 = impl_6__wrapping_shr x half in
  let yl:u8 = y &. lo_mask in
  let yh:u8 = impl_6__wrapping_shr y half in
  let ll:u8 = impl_6__wrapping_mul xl yl in
  let lh:u8 = impl_6__wrapping_mul xl yh in
  let hl:u8 = impl_6__wrapping_mul xh yl in
  let hh:u8 = impl_6__wrapping_mul xh yh in
  let mid:u8 =
    impl_6__wrapping_add (impl_6__wrapping_add (impl_6__wrapping_shr ll half <: u8)
          (lh &. lo_mask <: u8)
        <:
        u8)
      (hl &. lo_mask <: u8)
  in
  let low:u8 = (ll &. lo_mask <: u8) |. (impl_6__wrapping_shl (mid &. lo_mask <: u8) half <: u8) in
  let high:u8 =
    impl_6__wrapping_add (impl_6__wrapping_add (impl_6__wrapping_add hh
              (impl_6__wrapping_shr lh half <: u8)
            <:
            u8)
          (impl_6__wrapping_shr hl half <: u8)
        <:
        u8)
      (impl_6__wrapping_shr mid half <: u8)
  in
  low, high <: (u8 & u8)

/// See [`std::primitive::u8::carrying_mul_add`] (and similar for other unsigned integer types)
let impl_6__carrying_mul_add (x y carry add: u8) : (u8 & u8) =
  let (low: u8), (high: u8) = impl_6__widening_mul x y in
  let (low: u8), (c1: bool) = impl_6__overflowing_add low carry in
  let (low: u8), (c2: bool) = impl_6__overflowing_add low add in
  let high:u8 = impl_6__wrapping_add high (if c1 then mk_u8 1 else mk_u8 0) in
  let high:u8 = impl_6__wrapping_add high (if c2 then mk_u8 1 else mk_u8 0) in
  low, high <: (u8 & u8)

/// See [`std::primitive::u8::carrying_mul`] (and similar for other unsigned integer types)
let impl_6__carrying_mul (x y carry: u8) : (u8 & u8) = impl_6__carrying_mul_add x y carry (mk_u8 0)

/// See [`std::primitive::u8::carrying_add`] (and similar for other integer types)
let impl_6__carrying_add (x y: u8) (carry: bool) : (u8 & bool) =
  let (a: u8), (c1: bool) = impl_6__overflowing_add x y in
  let (b: u8), (c2: bool) = impl_6__overflowing_add a (if carry then mk_u8 1 else mk_u8 0) in
  b, c1 || c2 <: (u8 & bool)

/// See [`std::primitive::u8::borrowing_sub`] (and similar for other integer types)
let impl_6__borrowing_sub (x y: u8) (borrow: bool) : (u8 & bool) =
  let (a: u8), (c1: bool) = impl_6__overflowing_sub x y in
  let (b: u8), (c2: bool) = impl_6__overflowing_sub a (if borrow then mk_u8 1 else mk_u8 0) in
  b, c1 || c2 <: (u8 & bool)

/// See [`std::primitive::u8::is_ascii`]
let impl_6__is_ascii (x: u8) : bool = x <. mk_u8 128

/// See [`std::primitive::u8::is_ascii_uppercase`]
let impl_6__is_ascii_uppercase (x: u8) : bool = x >=. mk_u8 65 && x <=. mk_u8 90

/// See [`std::primitive::u8::is_ascii_lowercase`]
let impl_6__is_ascii_lowercase (x: u8) : bool = x >=. mk_u8 97 && x <=. mk_u8 122

/// See [`std::primitive::u8::is_ascii_alphabetic`]
let impl_6__is_ascii_alphabetic (x: u8) : bool =
  impl_6__is_ascii_uppercase x || impl_6__is_ascii_lowercase x

/// See [`std::primitive::u8::is_ascii_digit`]
let impl_6__is_ascii_digit (x: u8) : bool = x >=. mk_u8 48 && x <=. mk_u8 57

/// See [`std::primitive::u8::is_ascii_octdigit`]
let impl_6__is_ascii_octdigit (x: u8) : bool = x >=. mk_u8 48 && x <=. mk_u8 55

/// See [`std::primitive::u8::is_ascii_hexdigit`]
let impl_6__is_ascii_hexdigit (x: u8) : bool =
  impl_6__is_ascii_digit x || x >=. mk_u8 65 && x <=. mk_u8 70 || x >=. mk_u8 97 && x <=. mk_u8 102

/// See [`std::primitive::u8::is_ascii_alphanumeric`]
let impl_6__is_ascii_alphanumeric (x: u8) : bool =
  impl_6__is_ascii_alphabetic x || impl_6__is_ascii_digit x

/// See [`std::primitive::u8::is_ascii_punctuation`]
let impl_6__is_ascii_punctuation (x: u8) : bool =
  x >=. mk_u8 33 && x <=. mk_u8 47 || x >=. mk_u8 58 && x <=. mk_u8 64 ||
  x >=. mk_u8 91 && x <=. mk_u8 96 ||
  x >=. mk_u8 123 && x <=. mk_u8 126

/// See [`std::primitive::u8::is_ascii_graphic`]
let impl_6__is_ascii_graphic (x: u8) : bool = x >=. mk_u8 33 && x <=. mk_u8 126

/// See [`std::primitive::u8::is_ascii_whitespace`]
let impl_6__is_ascii_whitespace (x: u8) : bool =
  x =. mk_u8 32 || x =. mk_u8 9 || x =. mk_u8 10 || x =. mk_u8 12 || x =. mk_u8 13

/// See [`std::primitive::u8::is_ascii_control`]
let impl_6__is_ascii_control (x: u8) : bool = x <=. mk_u8 31 || x =. mk_u8 127

/// See [`std::primitive::u8::to_ascii_uppercase`]
let impl_6__to_ascii_uppercase (x: u8) : u8 =
  if x >=. mk_u8 97 && x <=. mk_u8 122 then x -! mk_u8 32 else x

/// See [`std::primitive::u8::to_ascii_lowercase`]
let impl_6__to_ascii_lowercase (x: u8) : u8 =
  if x >=. mk_u8 65 && x <=. mk_u8 90 then x +! mk_u8 32 else x

/// See [`std::primitive::u8::eq_ignore_ascii_case`]
let impl_6__eq_ignore_ascii_case (x other: u8) : bool =
  (impl_6__to_ascii_lowercase x <: u8) =. (impl_6__to_ascii_lowercase other <: u8)

/// See [`std::primitive::u8::make_ascii_uppercase`]
let impl_6__make_ascii_uppercase (x: u8) : u8 =
  let x:u8 = impl_6__to_ascii_uppercase x in
  x

/// See [`std::primitive::u8::make_ascii_lowercase`]
let impl_6__make_ascii_lowercase (x: u8) : u8 =
  let x:u8 = impl_6__to_ascii_lowercase x in
  x

/// See [`std::primitive::u8::unchecked_add`] (and similar for other integer types)
let impl_6__unchecked_add (x y: u8)
    : Prims.Pure u8
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_6__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) = x +! y

/// See [`std::primitive::u8::unchecked_sub`] (and similar for other integer types)
let impl_6__unchecked_sub (x y: u8) : Prims.Pure u8 (requires x >=. y) (fun _ -> Prims.l_True) =
  x -! y

/// See [`std::primitive::u8::unchecked_mul`] (and similar for other integer types)
let impl_6__unchecked_mul (x y: u8)
    : Prims.Pure u8
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_6__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) = x *! y

/// See [`std::primitive::u8::rem_euclid`] (and similar for other integer types)
let impl_6__rem_euclid (x y: u8) : Prims.Pure u8 (requires y <>. mk_u8 0) (fun _ -> Prims.l_True) =
  Rust_primitives.Arithmetic.rem_euclid_u8 x y

/// See [`std::primitive::u8::unchecked_div`] (and similar for other integer types)
let impl_6__unchecked_div (x y: u8) : Prims.Pure u8 (requires y <>. mk_u8 0) (fun _ -> Prims.l_True) =
  x /! y

/// See [`std::primitive::u8::unchecked_rem`] (and similar for other integer types)
let impl_6__unchecked_rem (x y: u8) : Prims.Pure u8 (requires y <>. mk_u8 0) (fun _ -> Prims.l_True) =
  x %! y

/// See [`std::primitive::u8::div_ceil`] (and similar for other unsigned integer types)
let impl_6__div_ceil (x y: u8) : Prims.Pure u8 (requires y <>. mk_u8 0) (fun _ -> Prims.l_True) =
  let d:u8 = x /! y in
  let r:u8 = x %! y in
  if r >. mk_u8 0 then d +! mk_u8 1 else d

/// See [`std::primitive::u8::strict_neg`] (and similar for other integer types)
let impl_6__strict_neg (x: u8) : Prims.Pure u8 (requires x =. mk_u8 0) (fun _ -> Prims.l_True) =
  if x =. mk_u8 0 then mk_u8 0 else Core_models.Panicking.Internal.panic #u8 ()

/// See [`std::primitive::u8::strict_pow`] (and similar for other integer types)
let impl_6__strict_pow (x: u8) (exp: u32)
    : Prims.Pure u8
      (requires (impl_6__overflowing_pow x exp <: (u8 & bool))._2 =. false)
      (fun _ -> Prims.l_True) =
  let (result: u8), (overflowed: bool) = impl_6__overflowing_pow x exp in
  if overflowed then Core_models.Panicking.Internal.panic #u8 () else result

/// See [`std::primitive::u8::strict_add`] (and similar for other integer types)
let impl_6__strict_add (x y: u8)
    : Prims.Pure u8
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_6__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: u8), (overflowed: bool) = impl_6__overflowing_add x y in
  if overflowed then Core_models.Panicking.Internal.panic #u8 () else result

/// See [`std::primitive::u8::strict_sub`] (and similar for other integer types)
let impl_6__strict_sub (x y: u8) : Prims.Pure u8 (requires x >=. y) (fun _ -> Prims.l_True) =
  let (result: u8), (overflowed: bool) = impl_6__overflowing_sub x y in
  if overflowed then Core_models.Panicking.Internal.panic #u8 () else result

/// See [`std::primitive::u8::strict_mul`] (and similar for other integer types)
let impl_6__strict_mul (x y: u8)
    : Prims.Pure u8
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_6__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: u8), (overflowed: bool) = impl_6__overflowing_mul x y in
  if overflowed then Core_models.Panicking.Internal.panic #u8 () else result

/// See [`std::primitive::u8::wrapping_div`] (and similar for other unsigned integer types)
let impl_6__wrapping_div (x y: u8) : Prims.Pure u8 (requires y <>. mk_u8 0) (fun _ -> Prims.l_True) =
  x /! y

/// See [`std::primitive::u8::wrapping_rem`] (and similar for other unsigned integer types)
let impl_6__wrapping_rem (x y: u8) : Prims.Pure u8 (requires y <>. mk_u8 0) (fun _ -> Prims.l_True) =
  x %! y

/// See [`std::primitive::u8::wrapping_div_euclid`] (and similar for other unsigned integer types)
let impl_6__wrapping_div_euclid (x y: u8)
    : Prims.Pure u8 (requires y <>. mk_u8 0) (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::wrapping_rem_euclid`] (and similar for other unsigned integer types)
let impl_6__wrapping_rem_euclid (x y: u8)
    : Prims.Pure u8 (requires y <>. mk_u8 0) (fun _ -> Prims.l_True) = x %! y

/// See [`std::primitive::u8::saturating_div`] (and similar for other unsigned integer types)
let impl_6__saturating_div (x y: u8)
    : Prims.Pure u8 (requires y <>. mk_u8 0) (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::strict_div`] (and similar for other unsigned integer types)
let impl_6__strict_div (x y: u8) : Prims.Pure u8 (requires y <>. mk_u8 0) (fun _ -> Prims.l_True) =
  x /! y

/// See [`std::primitive::u8::strict_rem`] (and similar for other unsigned integer types)
let impl_6__strict_rem (x y: u8) : Prims.Pure u8 (requires y <>. mk_u8 0) (fun _ -> Prims.l_True) =
  x %! y

/// See [`std::primitive::u8::strict_div_euclid`] (and similar for other unsigned integer types)
let impl_6__strict_div_euclid (x y: u8)
    : Prims.Pure u8 (requires y <>. mk_u8 0) (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::strict_rem_euclid`] (and similar for other unsigned integer types)
let impl_6__strict_rem_euclid (x y: u8)
    : Prims.Pure u8 (requires y <>. mk_u8 0) (fun _ -> Prims.l_True) = x %! y

/// See [`std::primitive::u8::div_euclid`] (and similar for other unsigned integer types)
let impl_6__div_euclid (x y: u8) : Prims.Pure u8 (requires y <>. mk_u8 0) (fun _ -> Prims.l_True) =
  x /! y

/// See [`std::primitive::u8::div_floor`] (and similar for other unsigned integer types)
let impl_6__div_floor (x y: u8) : Prims.Pure u8 (requires y <>. mk_u8 0) (fun _ -> Prims.l_True) =
  x /! y

/// See [`std::primitive::u8::overflowing_div`] (and similar for other unsigned integer types)
let impl_6__overflowing_div (x y: u8)
    : Prims.Pure (u8 & bool) (requires y <>. mk_u8 0) (fun _ -> Prims.l_True) =
  x /! y, false <: (u8 & bool)

/// See [`std::primitive::u8::overflowing_rem`] (and similar for other unsigned integer types)
let impl_6__overflowing_rem (x y: u8)
    : Prims.Pure (u8 & bool) (requires y <>. mk_u8 0) (fun _ -> Prims.l_True) =
  x %! y, false <: (u8 & bool)

/// See [`std::primitive::u8::overflowing_div_euclid`] (and similar for other unsigned integer types)
let impl_6__overflowing_div_euclid (x y: u8)
    : Prims.Pure (u8 & bool) (requires y <>. mk_u8 0) (fun _ -> Prims.l_True) =
  x /! y, false <: (u8 & bool)

/// See [`std::primitive::u8::overflowing_rem_euclid`] (and similar for other unsigned integer types)
let impl_6__overflowing_rem_euclid (x y: u8)
    : Prims.Pure (u8 & bool) (requires y <>. mk_u8 0) (fun _ -> Prims.l_True) =
  x %! y, false <: (u8 & bool)

/// See [`std::primitive::u8::unchecked_div_exact`] (and similar for other unsigned integer types)
let impl_6__unchecked_div_exact (x y: u8)
    : Prims.Pure u8 (requires y <>. mk_u8 0 && (x %! y <: u8) =. mk_u8 0) (fun _ -> Prims.l_True) =
  x /! y

/// See [`std::primitive::u8::next_multiple_of`] (and similar for other unsigned integer types)
let impl_6__next_multiple_of (x y: u8)
    : Prims.Pure u8
      (requires
        y <>. mk_u8 0 &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine ((y -! (x %! y <: u8) <: u8) %! y <: u8)
            <:
            Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_6__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) = x +! ((y -! (x %! y <: u8) <: u8) %! y <: u8)

/// See [`std::primitive::u8::strict_add_signed`] (and similar for other unsigned integer types)
let impl_6__strict_add_signed (x: u8) (y: i8)
    : Prims.Pure u8
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_6__MIN <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_6__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: u8), (overflowed: bool) = impl_6__overflowing_add_signed x y in
  if overflowed then Core_models.Panicking.Internal.panic #u8 () else result

/// See [`std::primitive::u8::strict_sub_signed`] (and similar for other unsigned integer types)
let impl_6__strict_sub_signed (x: u8) (y: i8)
    : Prims.Pure u8
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_6__MIN <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_6__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: u8), (overflowed: bool) = impl_6__overflowing_sub_signed x y in
  if overflowed then Core_models.Panicking.Internal.panic #u8 () else result

/// See [`std::primitive::u8::strict_shl`] (and similar for other integer types)
let impl_6__strict_shl (x: u8) (n: u32)
    : Prims.Pure u8 (requires n <. impl_6__BITS) (fun _ -> Prims.l_True) =
  if n <. impl_6__BITS then x <<! n else Core_models.Panicking.Internal.panic #u8 ()

/// See [`std::primitive::u8::strict_shr`] (and similar for other integer types)
let impl_6__strict_shr (x: u8) (n: u32)
    : Prims.Pure u8 (requires n <. impl_6__BITS) (fun _ -> Prims.l_True) =
  if n <. impl_6__BITS then x >>! n else Core_models.Panicking.Internal.panic #u8 ()

/// See [`std::primitive::u8::unchecked_shl`] (and similar for other integer types)
let impl_6__unchecked_shl (x: u8) (n: u32)
    : Prims.Pure u8 (requires n <. impl_6__BITS) (fun _ -> Prims.l_True) = x <<! n

/// See [`std::primitive::u8::unchecked_shr`] (and similar for other integer types)
let impl_6__unchecked_shr (x: u8) (n: u32)
    : Prims.Pure u8 (requires n <. impl_6__BITS) (fun _ -> Prims.l_True) = x >>! n

/// See [`std::primitive::u8::unchecked_shl_exact`] (and similar for other unsigned integer types)
let impl_6__unchecked_shl_exact (x: u8) (n: u32)
    : Prims.Pure u8
      (requires n <=. (impl_6__leading_zeros x <: u32) && n <. impl_6__BITS)
      (fun _ -> Prims.l_True) = x <<! n

/// See [`std::primitive::u8::unchecked_shr_exact`] (and similar for other integer types)
let impl_6__unchecked_shr_exact (x: u8) (n: u32)
    : Prims.Pure u8
      (requires n <=. (impl_6__trailing_zeros x <: u32) && n <. impl_6__BITS)
      (fun _ -> Prims.l_True) = x >>! n

/// See [`std::primitive::u8::funnel_shl`] (and similar for other unsigned integer types)
let impl_6__funnel_shl (x y: u8) (n: u32)
    : Prims.Pure u8 (requires n <. impl_6__BITS) (fun _ -> Prims.l_True) =
  if n =. mk_u32 0
  then x
  else (impl_6__wrapping_shl x n <: u8) |. (impl_6__wrapping_shr y (impl_6__BITS -! n <: u32) <: u8)

/// See [`std::primitive::u8::funnel_shr`] (and similar for other unsigned integer types)
let impl_6__funnel_shr (x y: u8) (n: u32)
    : Prims.Pure u8 (requires n <. impl_6__BITS) (fun _ -> Prims.l_True) =
  if n =. mk_u32 0
  then y
  else (impl_6__wrapping_shr y n <: u8) |. (impl_6__wrapping_shl x (impl_6__BITS -! n <: u32) <: u8)

/// See [`std::primitive::u8::unchecked_disjoint_bitor`] (and similar for other unsigned integer types)
let impl_6__unchecked_disjoint_bitor (x y: u8)
    : Prims.Pure u8 (requires (x &. y <: u8) =. mk_u8 0) (fun _ -> Prims.l_True) = x |. y

/// See [`std::primitive::u8::next_power_of_two`] (and similar for other unsigned integer types)
assume
val impl_6__next_power_of_two': x: u8
  -> Prims.Pure u8
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine (mk_i32 2) <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        ((Rust_primitives.Hax.Int.from_machine impl_6__MAX <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine (mk_i32 1) <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True)

unfold
let impl_6__next_power_of_two = impl_6__next_power_of_two'

/// See [`std::primitive::u8::MIN`] (and similar for other unsigned integer types)
let impl_7__MIN: u16 = mk_u16 0

/// See [`std::primitive::u8::MAX`] (and similar for other unsigned integer types)
let impl_7__MAX: u16 = mk_u16 65535

/// See [`std::primitive::u8::BITS`] (and similar for other unsigned integer types)
let impl_7__BITS: u32 = mk_u32 16

/// See [`std::primitive::u8::wrapping_add`] (and similar for other unsigned integer types)
let impl_7__wrapping_add (x y: u16) : u16 = Rust_primitives.Arithmetic.wrapping_add_u16 x y

/// See [`std::primitive::u8::saturating_add`] (and similar for other integer types)
let impl_7__saturating_add (x y: u16) : u16 = Rust_primitives.Arithmetic.saturating_add_u16 x y

/// See [`std::primitive::u8::overflowing_add`] (and similar for other integer types)
let impl_7__overflowing_add (x y: u16) : (u16 & bool) =
  Rust_primitives.Arithmetic.overflowing_add_u16 x y

/// See [`std::primitive::u8::wrapping_sub`] (and similar for other integer types)
let impl_7__wrapping_sub (x y: u16) : u16 = Rust_primitives.Arithmetic.wrapping_sub_u16 x y

/// See [`std::primitive::u8::saturating_sub`] (and similar for other integer types)
let impl_7__saturating_sub (x y: u16) : u16 = Rust_primitives.Arithmetic.saturating_sub_u16 x y

/// See [`std::primitive::u8::overflowing_sub`] (and similar for other integer types)
let impl_7__overflowing_sub (x y: u16) : (u16 & bool) =
  Rust_primitives.Arithmetic.overflowing_sub_u16 x y

/// See [`std::primitive::u8::wrapping_mul`] (and similar for other integer types)
let impl_7__wrapping_mul (x y: u16) : u16 = Rust_primitives.Arithmetic.wrapping_mul_u16 x y

/// See [`std::primitive::u8::saturating_mul`] (and similar for other integer types)
let impl_7__saturating_mul (x y: u16) : u16 = Rust_primitives.Arithmetic.saturating_mul_u16 x y

/// See [`std::primitive::u8::overflowing_mul`] (and similar for other integer types)
let impl_7__overflowing_mul (x y: u16) : (u16 & bool) =
  Rust_primitives.Arithmetic.overflowing_mul_u16 x y

/// See [`std::primitive::u8::pow`] (and similar for other integer types)
let impl_7__pow (x: u16) (exp: u32) : u16 = Rust_primitives.Arithmetic.pow_u16 x exp

/// See [`std::primitive::u8::overflowing_pow`] (and similar for other integer types)
let impl_7__overflowing_pow (x: u16) (exp: u32) : (u16 & bool) =
  Rust_primitives.Arithmetic.overflowing_pow_u16 x exp

/// See [`std::primitive::u8::count_ones`] (and similar for other integer types)
let impl_7__count_ones (x: u16) : u32 = Rust_primitives.Arithmetic.count_ones_u16 x

/// See [`std::primitive::u8::rotate_right`] (and similar for other integer types)
assume
val impl_7__rotate_right': x: u16 -> n: u32 -> u16

unfold
let impl_7__rotate_right = impl_7__rotate_right'

/// See [`std::primitive::u8::rotate_left`] (and similar for other integer types)
assume
val impl_7__rotate_left': x: u16 -> n: u32 -> u16

unfold
let impl_7__rotate_left = impl_7__rotate_left'

/// See [`std::primitive::u8::leading_zeros`] (and similar for other integer types)
assume
val impl_7__leading_zeros': x: u16 -> u32

unfold
let impl_7__leading_zeros = impl_7__leading_zeros'

/// See [`std::primitive::u8::ilog2`] (and similar for other integer types)
assume
val impl_7__ilog2': x: u16 -> u32

unfold
let impl_7__ilog2 = impl_7__ilog2'

/// See [`std::primitive::u8::from_be_bytes`] (and similar for other integer types)
assume
val impl_7__from_be_bytes': bytes: t_Array u8 (mk_usize 2) -> u16

unfold
let impl_7__from_be_bytes = impl_7__from_be_bytes'

/// See [`std::primitive::u8::from_le_bytes`] (and similar for other integer types)
assume
val impl_7__from_le_bytes': bytes: t_Array u8 (mk_usize 2) -> u16

unfold
let impl_7__from_le_bytes = impl_7__from_le_bytes'

/// See [`std::primitive::u8::to_be_bytes`] (and similar for other integer types)
assume
val impl_7__to_be_bytes': bytes: u16 -> t_Array u8 (mk_usize 2)

unfold
let impl_7__to_be_bytes = impl_7__to_be_bytes'

/// See [`std::primitive::u8::to_le_bytes`] (and similar for other integer types)
assume
val impl_7__to_le_bytes': bytes: u16 -> t_Array u8 (mk_usize 2)

unfold
let impl_7__to_le_bytes = impl_7__to_le_bytes'

/// See [`std::primitive::u8::is_power_of_two`] (and similar for other unsigned integer types)
let impl_7__is_power_of_two (x: u16) : bool =
  x <>. mk_u16 0 && (x &. (x -! mk_u16 1 <: u16) <: u16) =. mk_u16 0

/// See [`std::primitive::u8::is_multiple_of`] (and similar for other unsigned integer types)
let impl_7__is_multiple_of (x y: u16) : bool =
  if y =. mk_u16 0 then x =. mk_u16 0 else (x %! y <: u16) =. mk_u16 0

/// See [`std::primitive::u8::wrapping_neg`] (and similar for other integer types)
let impl_7__wrapping_neg (x: u16) : u16 = Rust_primitives.Arithmetic.wrapping_sub_u16 (mk_u16 0) x

/// See [`std::primitive::u8::min_value`] (and similar for other integer types)
let impl_7__min_value (_: Prims.unit) : u16 = impl_7__MIN

/// See [`std::primitive::u8::max_value`] (and similar for other integer types)
let impl_7__max_value (_: Prims.unit) : u16 = impl_7__MAX

/// See [`std::primitive::u8::cast_signed`] (and similar for other unsigned integer types)
let impl_7__cast_signed (x: u16) : i16 = cast (x <: u16) <: i16

/// See [`std::primitive::u8::count_zeros`] (and similar for other integer types)
let impl_7__count_zeros (x: u16) : u32 = impl_7__BITS -! (impl_7__count_ones x <: u32)

/// See [`std::primitive::u8::overflowing_neg`] (and similar for other integer types)
let impl_7__overflowing_neg (x: u16) : (u16 & bool) =
  impl_7__wrapping_neg x, x <>. mk_u16 0 <: (u16 & bool)

/// See [`std::primitive::u8::wrapping_pow`] (and similar for other integer types)
let impl_7__wrapping_pow (x: u16) (exp: u32) : u16 =
  let (result: u16), (_: bool) = impl_7__overflowing_pow x exp in
  result

/// See [`std::primitive::u8::saturating_pow`] (and similar for other unsigned integer types)
let impl_7__saturating_pow (x: u16) (exp: u32) : u16 =
  let (result: u16), (overflowed: bool) = impl_7__overflowing_pow x exp in
  if overflowed then impl_7__MAX else result

/// See [`std::primitive::u8::abs_diff`] (and similar for other unsigned integer types)
let impl_7__abs_diff (x y: u16) : u16 = if x <. y then y -! x else x -! y

/// See [`std::primitive::u8::midpoint`] (and similar for other unsigned integer types)
let impl_7__midpoint (x y: u16) : u16 =
  impl_7__wrapping_add ((x ^. y <: u16) >>! mk_i32 1 <: u16) (x &. y <: u16)

/// See [`std::primitive::u8::wrapping_add_signed`] (and similar for other unsigned integer types)
let impl_7__wrapping_add_signed (x: u16) (y: i16) : u16 =
  impl_7__wrapping_add x (cast (y <: i16) <: u16)

/// See [`std::primitive::u8::wrapping_sub_signed`] (and similar for other unsigned integer types)
let impl_7__wrapping_sub_signed (x: u16) (y: i16) : u16 =
  impl_7__wrapping_sub x (cast (y <: i16) <: u16)

/// See [`std::primitive::u8::overflowing_add_signed`] (and similar for other unsigned integer types)
let impl_7__overflowing_add_signed (x: u16) (y: i16) : (u16 & bool) =
  let (result: u16), (overflowed: bool) = impl_7__overflowing_add x (cast (y <: i16) <: u16) in
  result, overflowed <>. (y <. mk_i16 0 <: bool) <: (u16 & bool)

/// See [`std::primitive::u8::overflowing_sub_signed`] (and similar for other unsigned integer types)
let impl_7__overflowing_sub_signed (x: u16) (y: i16) : (u16 & bool) =
  let (result: u16), (overflowed: bool) = impl_7__overflowing_sub x (cast (y <: i16) <: u16) in
  result, overflowed <>. (y <. mk_i16 0 <: bool) <: (u16 & bool)

/// See [`std::primitive::u8::saturating_add_signed`] (and similar for other unsigned integer types)
let impl_7__saturating_add_signed (x: u16) (y: i16) : u16 =
  let (result: u16), (overflowed: bool) = impl_7__overflowing_add_signed x y in
  if ~.overflowed then result else if y <. mk_i16 0 then impl_7__MIN else impl_7__MAX

/// See [`std::primitive::u8::saturating_sub_signed`] (and similar for other unsigned integer types)
let impl_7__saturating_sub_signed (x: u16) (y: i16) : u16 =
  let (result: u16), (overflowed: bool) = impl_7__overflowing_sub_signed x y in
  if ~.overflowed then result else if y <. mk_i16 0 then impl_7__MAX else impl_7__MIN

/// See [`std::primitive::u8::trailing_zeros`] (and similar for other integer types)
let impl_7__trailing_zeros (x: u16) : u32 =
  if x =. mk_u16 0
  then impl_7__BITS
  else
    impl_7__count_ones (impl_7__wrapping_sub (x &. (impl_7__wrapping_neg x <: u16) <: u16)
          (mk_u16 1)
        <:
        u16)

/// See [`std::primitive::u8::trailing_ones`] (and similar for other integer types)
let impl_7__trailing_ones (x: u16) : u32 =
  impl_7__trailing_zeros (impl_7__wrapping_sub impl_7__MAX x <: u16)

/// See [`std::primitive::u8::leading_ones`] (and similar for other integer types)
let impl_7__leading_ones (x: u16) : u32 =
  impl_7__leading_zeros (impl_7__wrapping_sub impl_7__MAX x <: u16)

/// See [`std::primitive::u8::bit_width`] (and similar for other unsigned integer types)
assume
val impl_7__bit_width': x: u16 -> u32

unfold
let impl_7__bit_width = impl_7__bit_width'

/// See [`std::primitive::u8::isolate_lowest_one`] (and similar for other integer types)
let impl_7__isolate_lowest_one (x: u16) : u16 = x &. (impl_7__wrapping_neg x <: u16)

/// See [`std::primitive::u8::swap_bytes`] (and similar for other integer types)
let impl_7__swap_bytes (x: u16) : u16 =
  impl_7__from_le_bytes (impl_7__to_be_bytes x <: t_Array u8 (mk_usize 2))

/// See [`std::primitive::u8::to_be`] (and similar for other integer types)
let impl_7__to_be (x: u16) : u16 = impl_7__swap_bytes x

/// See [`std::primitive::u8::to_le`] (and similar for other integer types)
let impl_7__to_le (x: u16) : u16 = x

/// See [`std::primitive::u8::from_be`] (and similar for other integer types)
let impl_7__from_be (x: u16) : u16 = impl_7__swap_bytes x

/// See [`std::primitive::u8::from_le`] (and similar for other integer types)
let impl_7__from_le (x: u16) : u16 = x

/// See [`std::primitive::u8::to_ne_bytes`] (and similar for other integer types)
let impl_7__to_ne_bytes (x: u16) : t_Array u8 (mk_usize 2) = impl_7__to_le_bytes x

/// See [`std::primitive::u8::from_ne_bytes`] (and similar for other integer types)
let impl_7__from_ne_bytes (bytes: t_Array u8 (mk_usize 2)) : u16 = impl_7__from_le_bytes bytes

/// See [`std::primitive::u8::wrapping_shl`] (and similar for other integer types)
let impl_7__wrapping_shl (x: u16) (n: u32) : u16 = x <<! (n %! impl_7__BITS <: u32)

/// See [`std::primitive::u8::wrapping_shr`] (and similar for other integer types)
let impl_7__wrapping_shr (x: u16) (n: u32) : u16 = x >>! (n %! impl_7__BITS <: u32)

/// See [`std::primitive::u8::isolate_highest_one`] (and similar for other integer types)
let impl_7__isolate_highest_one (x: u16) : u16 =
  x &.
  (impl_7__wrapping_shr ((impl_7__MAX /! mk_u16 2 <: u16) +! mk_u16 1 <: u16)
      (impl_7__leading_zeros x <: u32)
    <:
    u16)

/// See [`std::primitive::u8::overflowing_shl`] (and similar for other integer types)
let impl_7__overflowing_shl (x: u16) (n: u32) : (u16 & bool) =
  impl_7__wrapping_shl x n, n >=. impl_7__BITS <: (u16 & bool)

/// See [`std::primitive::u8::overflowing_shr`] (and similar for other integer types)
let impl_7__overflowing_shr (x: u16) (n: u32) : (u16 & bool) =
  impl_7__wrapping_shr x n, n >=. impl_7__BITS <: (u16 & bool)

/// See [`std::primitive::u8::unbounded_shl`] (and similar for other integer types)
let impl_7__unbounded_shl (x: u16) (n: u32) : u16 = if n <. impl_7__BITS then x <<! n else mk_u16 0

/// See [`std::primitive::u8::unbounded_shr`] (and similar for other unsigned integer types)
let impl_7__unbounded_shr (x: u16) (n: u32) : u16 = if n <. impl_7__BITS then x >>! n else mk_u16 0

/// See [`std::primitive::u8::wrapping_next_power_of_two`] (and similar for other unsigned integer types)
let impl_7__wrapping_next_power_of_two (x: u16) : u16 =
  if x <=. mk_u16 1
  then mk_u16 1
  else
    impl_7__wrapping_add (impl_7__MAX >>!
        ((impl_7__leading_zeros (x -! mk_u16 1 <: u16) <: u32) %! impl_7__BITS <: u32)
        <:
        u16)
      (mk_u16 1)

/// See [`std::primitive::u8::reverse_bits`] (and similar for other unsigned integer types)
let impl_7__reverse_bits (x: u16) : u16 =
  let m1:u16 = impl_7__MAX /! mk_u16 3 in
  let m2:u16 = impl_7__MAX /! mk_u16 5 in
  let m4:u16 = impl_7__MAX /! mk_u16 17 in
  let x:u16 =
    (impl_7__wrapping_shl (x &. m1 <: u16) (mk_u32 1) <: u16) |.
    ((impl_7__wrapping_shr x (mk_u32 1) <: u16) &. m1 <: u16)
  in
  let x:u16 =
    (impl_7__wrapping_shl (x &. m2 <: u16) (mk_u32 2) <: u16) |.
    ((impl_7__wrapping_shr x (mk_u32 2) <: u16) &. m2 <: u16)
  in
  let x:u16 =
    (impl_7__wrapping_shl (x &. m4 <: u16) (mk_u32 4) <: u16) |.
    ((impl_7__wrapping_shr x (mk_u32 4) <: u16) &. m4 <: u16)
  in
  impl_7__swap_bytes x

/// See [`std::primitive::u8::widening_mul`] (and similar for other unsigned integer types)
let impl_7__widening_mul (x y: u16) : (u16 & u16) =
  let half:u32 = impl_7__BITS /! mk_u32 2 in
  let lo_mask:u16 = impl_7__wrapping_shr impl_7__MAX half in
  let xl:u16 = x &. lo_mask in
  let xh:u16 = impl_7__wrapping_shr x half in
  let yl:u16 = y &. lo_mask in
  let yh:u16 = impl_7__wrapping_shr y half in
  let ll:u16 = impl_7__wrapping_mul xl yl in
  let lh:u16 = impl_7__wrapping_mul xl yh in
  let hl:u16 = impl_7__wrapping_mul xh yl in
  let hh:u16 = impl_7__wrapping_mul xh yh in
  let mid:u16 =
    impl_7__wrapping_add (impl_7__wrapping_add (impl_7__wrapping_shr ll half <: u16)
          (lh &. lo_mask <: u16)
        <:
        u16)
      (hl &. lo_mask <: u16)
  in
  let low:u16 =
    (ll &. lo_mask <: u16) |. (impl_7__wrapping_shl (mid &. lo_mask <: u16) half <: u16)
  in
  let high:u16 =
    impl_7__wrapping_add (impl_7__wrapping_add (impl_7__wrapping_add hh
              (impl_7__wrapping_shr lh half <: u16)
            <:
            u16)
          (impl_7__wrapping_shr hl half <: u16)
        <:
        u16)
      (impl_7__wrapping_shr mid half <: u16)
  in
  low, high <: (u16 & u16)

/// See [`std::primitive::u8::carrying_mul_add`] (and similar for other unsigned integer types)
let impl_7__carrying_mul_add (x y carry add: u16) : (u16 & u16) =
  let (low: u16), (high: u16) = impl_7__widening_mul x y in
  let (low: u16), (c1: bool) = impl_7__overflowing_add low carry in
  let (low: u16), (c2: bool) = impl_7__overflowing_add low add in
  let high:u16 = impl_7__wrapping_add high (if c1 then mk_u16 1 else mk_u16 0) in
  let high:u16 = impl_7__wrapping_add high (if c2 then mk_u16 1 else mk_u16 0) in
  low, high <: (u16 & u16)

/// See [`std::primitive::u8::carrying_mul`] (and similar for other unsigned integer types)
let impl_7__carrying_mul (x y carry: u16) : (u16 & u16) =
  impl_7__carrying_mul_add x y carry (mk_u16 0)

/// See [`std::primitive::u8::carrying_add`] (and similar for other integer types)
let impl_7__carrying_add (x y: u16) (carry: bool) : (u16 & bool) =
  let (a: u16), (c1: bool) = impl_7__overflowing_add x y in
  let (b: u16), (c2: bool) = impl_7__overflowing_add a (if carry then mk_u16 1 else mk_u16 0) in
  b, c1 || c2 <: (u16 & bool)

/// See [`std::primitive::u8::borrowing_sub`] (and similar for other integer types)
let impl_7__borrowing_sub (x y: u16) (borrow: bool) : (u16 & bool) =
  let (a: u16), (c1: bool) = impl_7__overflowing_sub x y in
  let (b: u16), (c2: bool) = impl_7__overflowing_sub a (if borrow then mk_u16 1 else mk_u16 0) in
  b, c1 || c2 <: (u16 & bool)

/// See [`std::primitive::u16::is_utf16_surrogate`]
let impl_7__is_utf16_surrogate (x: u16) : bool = x >=. mk_u16 55296 && x <=. mk_u16 57343

/// See [`std::primitive::u8::unchecked_add`] (and similar for other integer types)
let impl_7__unchecked_add (x y: u16)
    : Prims.Pure u16
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_7__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) = x +! y

/// See [`std::primitive::u8::unchecked_sub`] (and similar for other integer types)
let impl_7__unchecked_sub (x y: u16) : Prims.Pure u16 (requires x >=. y) (fun _ -> Prims.l_True) =
  x -! y

/// See [`std::primitive::u8::unchecked_mul`] (and similar for other integer types)
let impl_7__unchecked_mul (x y: u16)
    : Prims.Pure u16
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_7__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) = x *! y

/// See [`std::primitive::u8::rem_euclid`] (and similar for other integer types)
let impl_7__rem_euclid (x y: u16) : Prims.Pure u16 (requires y <>. mk_u16 0) (fun _ -> Prims.l_True) =
  Rust_primitives.Arithmetic.rem_euclid_u16 x y

/// See [`std::primitive::u8::unchecked_div`] (and similar for other integer types)
let impl_7__unchecked_div (x y: u16)
    : Prims.Pure u16 (requires y <>. mk_u16 0) (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::unchecked_rem`] (and similar for other integer types)
let impl_7__unchecked_rem (x y: u16)
    : Prims.Pure u16 (requires y <>. mk_u16 0) (fun _ -> Prims.l_True) = x %! y

/// See [`std::primitive::u8::div_ceil`] (and similar for other unsigned integer types)
let impl_7__div_ceil (x y: u16) : Prims.Pure u16 (requires y <>. mk_u16 0) (fun _ -> Prims.l_True) =
  let d:u16 = x /! y in
  let r:u16 = x %! y in
  if r >. mk_u16 0 then d +! mk_u16 1 else d

/// See [`std::primitive::u8::strict_neg`] (and similar for other integer types)
let impl_7__strict_neg (x: u16) : Prims.Pure u16 (requires x =. mk_u16 0) (fun _ -> Prims.l_True) =
  if x =. mk_u16 0 then mk_u16 0 else Core_models.Panicking.Internal.panic #u16 ()

/// See [`std::primitive::u8::strict_pow`] (and similar for other integer types)
let impl_7__strict_pow (x: u16) (exp: u32)
    : Prims.Pure u16
      (requires (impl_7__overflowing_pow x exp <: (u16 & bool))._2 =. false)
      (fun _ -> Prims.l_True) =
  let (result: u16), (overflowed: bool) = impl_7__overflowing_pow x exp in
  if overflowed then Core_models.Panicking.Internal.panic #u16 () else result

/// See [`std::primitive::u8::strict_add`] (and similar for other integer types)
let impl_7__strict_add (x y: u16)
    : Prims.Pure u16
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_7__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: u16), (overflowed: bool) = impl_7__overflowing_add x y in
  if overflowed then Core_models.Panicking.Internal.panic #u16 () else result

/// See [`std::primitive::u8::strict_sub`] (and similar for other integer types)
let impl_7__strict_sub (x y: u16) : Prims.Pure u16 (requires x >=. y) (fun _ -> Prims.l_True) =
  let (result: u16), (overflowed: bool) = impl_7__overflowing_sub x y in
  if overflowed then Core_models.Panicking.Internal.panic #u16 () else result

/// See [`std::primitive::u8::strict_mul`] (and similar for other integer types)
let impl_7__strict_mul (x y: u16)
    : Prims.Pure u16
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_7__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: u16), (overflowed: bool) = impl_7__overflowing_mul x y in
  if overflowed then Core_models.Panicking.Internal.panic #u16 () else result

/// See [`std::primitive::u8::wrapping_div`] (and similar for other unsigned integer types)
let impl_7__wrapping_div (x y: u16)
    : Prims.Pure u16 (requires y <>. mk_u16 0) (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::wrapping_rem`] (and similar for other unsigned integer types)
let impl_7__wrapping_rem (x y: u16)
    : Prims.Pure u16 (requires y <>. mk_u16 0) (fun _ -> Prims.l_True) = x %! y

/// See [`std::primitive::u8::wrapping_div_euclid`] (and similar for other unsigned integer types)
let impl_7__wrapping_div_euclid (x y: u16)
    : Prims.Pure u16 (requires y <>. mk_u16 0) (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::wrapping_rem_euclid`] (and similar for other unsigned integer types)
let impl_7__wrapping_rem_euclid (x y: u16)
    : Prims.Pure u16 (requires y <>. mk_u16 0) (fun _ -> Prims.l_True) = x %! y

/// See [`std::primitive::u8::saturating_div`] (and similar for other unsigned integer types)
let impl_7__saturating_div (x y: u16)
    : Prims.Pure u16 (requires y <>. mk_u16 0) (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::strict_div`] (and similar for other unsigned integer types)
let impl_7__strict_div (x y: u16) : Prims.Pure u16 (requires y <>. mk_u16 0) (fun _ -> Prims.l_True) =
  x /! y

/// See [`std::primitive::u8::strict_rem`] (and similar for other unsigned integer types)
let impl_7__strict_rem (x y: u16) : Prims.Pure u16 (requires y <>. mk_u16 0) (fun _ -> Prims.l_True) =
  x %! y

/// See [`std::primitive::u8::strict_div_euclid`] (and similar for other unsigned integer types)
let impl_7__strict_div_euclid (x y: u16)
    : Prims.Pure u16 (requires y <>. mk_u16 0) (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::strict_rem_euclid`] (and similar for other unsigned integer types)
let impl_7__strict_rem_euclid (x y: u16)
    : Prims.Pure u16 (requires y <>. mk_u16 0) (fun _ -> Prims.l_True) = x %! y

/// See [`std::primitive::u8::div_euclid`] (and similar for other unsigned integer types)
let impl_7__div_euclid (x y: u16) : Prims.Pure u16 (requires y <>. mk_u16 0) (fun _ -> Prims.l_True) =
  x /! y

/// See [`std::primitive::u8::div_floor`] (and similar for other unsigned integer types)
let impl_7__div_floor (x y: u16) : Prims.Pure u16 (requires y <>. mk_u16 0) (fun _ -> Prims.l_True) =
  x /! y

/// See [`std::primitive::u8::overflowing_div`] (and similar for other unsigned integer types)
let impl_7__overflowing_div (x y: u16)
    : Prims.Pure (u16 & bool) (requires y <>. mk_u16 0) (fun _ -> Prims.l_True) =
  x /! y, false <: (u16 & bool)

/// See [`std::primitive::u8::overflowing_rem`] (and similar for other unsigned integer types)
let impl_7__overflowing_rem (x y: u16)
    : Prims.Pure (u16 & bool) (requires y <>. mk_u16 0) (fun _ -> Prims.l_True) =
  x %! y, false <: (u16 & bool)

/// See [`std::primitive::u8::overflowing_div_euclid`] (and similar for other unsigned integer types)
let impl_7__overflowing_div_euclid (x y: u16)
    : Prims.Pure (u16 & bool) (requires y <>. mk_u16 0) (fun _ -> Prims.l_True) =
  x /! y, false <: (u16 & bool)

/// See [`std::primitive::u8::overflowing_rem_euclid`] (and similar for other unsigned integer types)
let impl_7__overflowing_rem_euclid (x y: u16)
    : Prims.Pure (u16 & bool) (requires y <>. mk_u16 0) (fun _ -> Prims.l_True) =
  x %! y, false <: (u16 & bool)

/// See [`std::primitive::u8::unchecked_div_exact`] (and similar for other unsigned integer types)
let impl_7__unchecked_div_exact (x y: u16)
    : Prims.Pure u16
      (requires y <>. mk_u16 0 && (x %! y <: u16) =. mk_u16 0)
      (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::next_multiple_of`] (and similar for other unsigned integer types)
let impl_7__next_multiple_of (x y: u16)
    : Prims.Pure u16
      (requires
        y <>. mk_u16 0 &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine ((y -! (x %! y <: u16) <: u16) %! y <: u16)
            <:
            Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_7__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) = x +! ((y -! (x %! y <: u16) <: u16) %! y <: u16)

/// See [`std::primitive::u8::strict_add_signed`] (and similar for other unsigned integer types)
let impl_7__strict_add_signed (x: u16) (y: i16)
    : Prims.Pure u16
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_7__MIN <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_7__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: u16), (overflowed: bool) = impl_7__overflowing_add_signed x y in
  if overflowed then Core_models.Panicking.Internal.panic #u16 () else result

/// See [`std::primitive::u8::strict_sub_signed`] (and similar for other unsigned integer types)
let impl_7__strict_sub_signed (x: u16) (y: i16)
    : Prims.Pure u16
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_7__MIN <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_7__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: u16), (overflowed: bool) = impl_7__overflowing_sub_signed x y in
  if overflowed then Core_models.Panicking.Internal.panic #u16 () else result

/// See [`std::primitive::u8::strict_shl`] (and similar for other integer types)
let impl_7__strict_shl (x: u16) (n: u32)
    : Prims.Pure u16 (requires n <. impl_7__BITS) (fun _ -> Prims.l_True) =
  if n <. impl_7__BITS then x <<! n else Core_models.Panicking.Internal.panic #u16 ()

/// See [`std::primitive::u8::strict_shr`] (and similar for other integer types)
let impl_7__strict_shr (x: u16) (n: u32)
    : Prims.Pure u16 (requires n <. impl_7__BITS) (fun _ -> Prims.l_True) =
  if n <. impl_7__BITS then x >>! n else Core_models.Panicking.Internal.panic #u16 ()

/// See [`std::primitive::u8::unchecked_shl`] (and similar for other integer types)
let impl_7__unchecked_shl (x: u16) (n: u32)
    : Prims.Pure u16 (requires n <. impl_7__BITS) (fun _ -> Prims.l_True) = x <<! n

/// See [`std::primitive::u8::unchecked_shr`] (and similar for other integer types)
let impl_7__unchecked_shr (x: u16) (n: u32)
    : Prims.Pure u16 (requires n <. impl_7__BITS) (fun _ -> Prims.l_True) = x >>! n

/// See [`std::primitive::u8::unchecked_shl_exact`] (and similar for other unsigned integer types)
let impl_7__unchecked_shl_exact (x: u16) (n: u32)
    : Prims.Pure u16
      (requires n <=. (impl_7__leading_zeros x <: u32) && n <. impl_7__BITS)
      (fun _ -> Prims.l_True) = x <<! n

/// See [`std::primitive::u8::unchecked_shr_exact`] (and similar for other integer types)
let impl_7__unchecked_shr_exact (x: u16) (n: u32)
    : Prims.Pure u16
      (requires n <=. (impl_7__trailing_zeros x <: u32) && n <. impl_7__BITS)
      (fun _ -> Prims.l_True) = x >>! n

/// See [`std::primitive::u8::funnel_shl`] (and similar for other unsigned integer types)
let impl_7__funnel_shl (x y: u16) (n: u32)
    : Prims.Pure u16 (requires n <. impl_7__BITS) (fun _ -> Prims.l_True) =
  if n =. mk_u32 0
  then x
  else
    (impl_7__wrapping_shl x n <: u16) |. (impl_7__wrapping_shr y (impl_7__BITS -! n <: u32) <: u16)

/// See [`std::primitive::u8::funnel_shr`] (and similar for other unsigned integer types)
let impl_7__funnel_shr (x y: u16) (n: u32)
    : Prims.Pure u16 (requires n <. impl_7__BITS) (fun _ -> Prims.l_True) =
  if n =. mk_u32 0
  then y
  else
    (impl_7__wrapping_shr y n <: u16) |. (impl_7__wrapping_shl x (impl_7__BITS -! n <: u32) <: u16)

/// See [`std::primitive::u8::unchecked_disjoint_bitor`] (and similar for other unsigned integer types)
let impl_7__unchecked_disjoint_bitor (x y: u16)
    : Prims.Pure u16 (requires (x &. y <: u16) =. mk_u16 0) (fun _ -> Prims.l_True) = x |. y

/// See [`std::primitive::u8::next_power_of_two`] (and similar for other unsigned integer types)
assume
val impl_7__next_power_of_two': x: u16
  -> Prims.Pure u16
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine (mk_i32 2) <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        ((Rust_primitives.Hax.Int.from_machine impl_7__MAX <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine (mk_i32 1) <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True)

unfold
let impl_7__next_power_of_two = impl_7__next_power_of_two'

/// See [`std::primitive::u8::MIN`] (and similar for other unsigned integer types)
let impl_8__MIN: u32 = mk_u32 0

/// See [`std::primitive::u8::MAX`] (and similar for other unsigned integer types)
let impl_8__MAX: u32 = mk_u32 4294967295

/// See [`std::primitive::u8::BITS`] (and similar for other unsigned integer types)
let impl_8__BITS: u32 = mk_u32 32

/// See [`std::primitive::u8::wrapping_add`] (and similar for other unsigned integer types)
let impl_8__wrapping_add (x y: u32) : u32 = Rust_primitives.Arithmetic.wrapping_add_u32 x y

/// See [`std::primitive::u8::saturating_add`] (and similar for other integer types)
let impl_8__saturating_add (x y: u32) : u32 = Rust_primitives.Arithmetic.saturating_add_u32 x y

/// See [`std::primitive::u8::overflowing_add`] (and similar for other integer types)
let impl_8__overflowing_add (x y: u32) : (u32 & bool) =
  Rust_primitives.Arithmetic.overflowing_add_u32 x y

/// See [`std::primitive::u8::wrapping_sub`] (and similar for other integer types)
let impl_8__wrapping_sub (x y: u32) : u32 = Rust_primitives.Arithmetic.wrapping_sub_u32 x y

/// See [`std::primitive::u8::saturating_sub`] (and similar for other integer types)
let impl_8__saturating_sub (x y: u32) : u32 = Rust_primitives.Arithmetic.saturating_sub_u32 x y

/// See [`std::primitive::u8::overflowing_sub`] (and similar for other integer types)
let impl_8__overflowing_sub (x y: u32) : (u32 & bool) =
  Rust_primitives.Arithmetic.overflowing_sub_u32 x y

/// See [`std::primitive::u8::wrapping_mul`] (and similar for other integer types)
let impl_8__wrapping_mul (x y: u32) : u32 = Rust_primitives.Arithmetic.wrapping_mul_u32 x y

/// See [`std::primitive::u8::saturating_mul`] (and similar for other integer types)
let impl_8__saturating_mul (x y: u32) : u32 = Rust_primitives.Arithmetic.saturating_mul_u32 x y

/// See [`std::primitive::u8::overflowing_mul`] (and similar for other integer types)
let impl_8__overflowing_mul (x y: u32) : (u32 & bool) =
  Rust_primitives.Arithmetic.overflowing_mul_u32 x y

/// See [`std::primitive::u8::pow`] (and similar for other integer types)
let impl_8__pow (x exp: u32) : u32 = Rust_primitives.Arithmetic.pow_u32 x exp

/// See [`std::primitive::u8::overflowing_pow`] (and similar for other integer types)
let impl_8__overflowing_pow (x exp: u32) : (u32 & bool) =
  Rust_primitives.Arithmetic.overflowing_pow_u32 x exp

/// See [`std::primitive::u8::count_ones`] (and similar for other integer types)
let impl_8__count_ones (x: u32) : u32 = Rust_primitives.Arithmetic.count_ones_u32 x

/// See [`std::primitive::u8::rotate_right`] (and similar for other integer types)
assume
val impl_8__rotate_right': x: u32 -> n: u32 -> u32

unfold
let impl_8__rotate_right = impl_8__rotate_right'

/// See [`std::primitive::u8::rotate_left`] (and similar for other integer types)
assume
val impl_8__rotate_left': x: u32 -> n: u32 -> u32

unfold
let impl_8__rotate_left = impl_8__rotate_left'

/// See [`std::primitive::u8::leading_zeros`] (and similar for other integer types)
assume
val impl_8__leading_zeros': x: u32 -> u32

unfold
let impl_8__leading_zeros = impl_8__leading_zeros'

/// See [`std::primitive::u8::ilog2`] (and similar for other integer types)
assume
val impl_8__ilog2': x: u32 -> u32

unfold
let impl_8__ilog2 = impl_8__ilog2'

/// See [`std::primitive::u8::from_be_bytes`] (and similar for other integer types)
assume
val impl_8__from_be_bytes': bytes: t_Array u8 (mk_usize 4) -> u32

unfold
let impl_8__from_be_bytes = impl_8__from_be_bytes'

/// See [`std::primitive::u8::from_le_bytes`] (and similar for other integer types)
assume
val impl_8__from_le_bytes': bytes: t_Array u8 (mk_usize 4) -> u32

unfold
let impl_8__from_le_bytes = impl_8__from_le_bytes'

/// See [`std::primitive::u8::to_be_bytes`] (and similar for other integer types)
assume
val impl_8__to_be_bytes': bytes: u32 -> t_Array u8 (mk_usize 4)

unfold
let impl_8__to_be_bytes = impl_8__to_be_bytes'

/// See [`std::primitive::u8::to_le_bytes`] (and similar for other integer types)
assume
val impl_8__to_le_bytes': bytes: u32 -> t_Array u8 (mk_usize 4)

unfold
let impl_8__to_le_bytes = impl_8__to_le_bytes'

/// See [`std::primitive::u8::is_power_of_two`] (and similar for other unsigned integer types)
let impl_8__is_power_of_two (x: u32) : bool =
  x <>. mk_u32 0 && (x &. (x -! mk_u32 1 <: u32) <: u32) =. mk_u32 0

/// See [`std::primitive::u8::is_multiple_of`] (and similar for other unsigned integer types)
let impl_8__is_multiple_of (x y: u32) : bool =
  if y =. mk_u32 0 then x =. mk_u32 0 else (x %! y <: u32) =. mk_u32 0

/// See [`std::primitive::u8::wrapping_neg`] (and similar for other integer types)
let impl_8__wrapping_neg (x: u32) : u32 = Rust_primitives.Arithmetic.wrapping_sub_u32 (mk_u32 0) x

/// See [`std::primitive::u8::min_value`] (and similar for other integer types)
let impl_8__min_value (_: Prims.unit) : u32 = impl_8__MIN

/// See [`std::primitive::u8::max_value`] (and similar for other integer types)
let impl_8__max_value (_: Prims.unit) : u32 = impl_8__MAX

/// See [`std::primitive::u8::cast_signed`] (and similar for other unsigned integer types)
let impl_8__cast_signed (x: u32) : i32 = cast (x <: u32) <: i32

/// See [`std::primitive::u8::count_zeros`] (and similar for other integer types)
let impl_8__count_zeros (x: u32) : u32 = impl_8__BITS -! (impl_8__count_ones x <: u32)

/// See [`std::primitive::u8::overflowing_neg`] (and similar for other integer types)
let impl_8__overflowing_neg (x: u32) : (u32 & bool) =
  impl_8__wrapping_neg x, x <>. mk_u32 0 <: (u32 & bool)

/// See [`std::primitive::u8::wrapping_pow`] (and similar for other integer types)
let impl_8__wrapping_pow (x exp: u32) : u32 =
  let (result: u32), (_: bool) = impl_8__overflowing_pow x exp in
  result

/// See [`std::primitive::u8::saturating_pow`] (and similar for other unsigned integer types)
let impl_8__saturating_pow (x exp: u32) : u32 =
  let (result: u32), (overflowed: bool) = impl_8__overflowing_pow x exp in
  if overflowed then impl_8__MAX else result

/// See [`std::primitive::u8::abs_diff`] (and similar for other unsigned integer types)
let impl_8__abs_diff (x y: u32) : u32 = if x <. y then y -! x else x -! y

/// See [`std::primitive::u8::midpoint`] (and similar for other unsigned integer types)
let impl_8__midpoint (x y: u32) : u32 =
  impl_8__wrapping_add ((x ^. y <: u32) >>! mk_i32 1 <: u32) (x &. y <: u32)

/// See [`std::primitive::u8::wrapping_add_signed`] (and similar for other unsigned integer types)
let impl_8__wrapping_add_signed (x: u32) (y: i32) : u32 =
  impl_8__wrapping_add x (cast (y <: i32) <: u32)

/// See [`std::primitive::u8::wrapping_sub_signed`] (and similar for other unsigned integer types)
let impl_8__wrapping_sub_signed (x: u32) (y: i32) : u32 =
  impl_8__wrapping_sub x (cast (y <: i32) <: u32)

/// See [`std::primitive::u8::overflowing_add_signed`] (and similar for other unsigned integer types)
let impl_8__overflowing_add_signed (x: u32) (y: i32) : (u32 & bool) =
  let (result: u32), (overflowed: bool) = impl_8__overflowing_add x (cast (y <: i32) <: u32) in
  result, overflowed <>. (y <. mk_i32 0 <: bool) <: (u32 & bool)

/// See [`std::primitive::u8::overflowing_sub_signed`] (and similar for other unsigned integer types)
let impl_8__overflowing_sub_signed (x: u32) (y: i32) : (u32 & bool) =
  let (result: u32), (overflowed: bool) = impl_8__overflowing_sub x (cast (y <: i32) <: u32) in
  result, overflowed <>. (y <. mk_i32 0 <: bool) <: (u32 & bool)

/// See [`std::primitive::u8::saturating_add_signed`] (and similar for other unsigned integer types)
let impl_8__saturating_add_signed (x: u32) (y: i32) : u32 =
  let (result: u32), (overflowed: bool) = impl_8__overflowing_add_signed x y in
  if ~.overflowed then result else if y <. mk_i32 0 then impl_8__MIN else impl_8__MAX

/// See [`std::primitive::u8::saturating_sub_signed`] (and similar for other unsigned integer types)
let impl_8__saturating_sub_signed (x: u32) (y: i32) : u32 =
  let (result: u32), (overflowed: bool) = impl_8__overflowing_sub_signed x y in
  if ~.overflowed then result else if y <. mk_i32 0 then impl_8__MAX else impl_8__MIN

/// See [`std::primitive::u8::trailing_zeros`] (and similar for other integer types)
let impl_8__trailing_zeros (x: u32) : u32 =
  if x =. mk_u32 0
  then impl_8__BITS
  else
    impl_8__count_ones (impl_8__wrapping_sub (x &. (impl_8__wrapping_neg x <: u32) <: u32)
          (mk_u32 1)
        <:
        u32)

/// See [`std::primitive::u8::trailing_ones`] (and similar for other integer types)
let impl_8__trailing_ones (x: u32) : u32 =
  impl_8__trailing_zeros (impl_8__wrapping_sub impl_8__MAX x <: u32)

/// See [`std::primitive::u8::leading_ones`] (and similar for other integer types)
let impl_8__leading_ones (x: u32) : u32 =
  impl_8__leading_zeros (impl_8__wrapping_sub impl_8__MAX x <: u32)

/// See [`std::primitive::u8::bit_width`] (and similar for other unsigned integer types)
assume
val impl_8__bit_width': x: u32 -> u32

unfold
let impl_8__bit_width = impl_8__bit_width'

/// See [`std::primitive::u8::isolate_lowest_one`] (and similar for other integer types)
let impl_8__isolate_lowest_one (x: u32) : u32 = x &. (impl_8__wrapping_neg x <: u32)

/// See [`std::primitive::u8::swap_bytes`] (and similar for other integer types)
let impl_8__swap_bytes (x: u32) : u32 =
  impl_8__from_le_bytes (impl_8__to_be_bytes x <: t_Array u8 (mk_usize 4))

/// See [`std::primitive::u8::to_be`] (and similar for other integer types)
let impl_8__to_be (x: u32) : u32 = impl_8__swap_bytes x

/// See [`std::primitive::u8::to_le`] (and similar for other integer types)
let impl_8__to_le (x: u32) : u32 = x

/// See [`std::primitive::u8::from_be`] (and similar for other integer types)
let impl_8__from_be (x: u32) : u32 = impl_8__swap_bytes x

/// See [`std::primitive::u8::from_le`] (and similar for other integer types)
let impl_8__from_le (x: u32) : u32 = x

/// See [`std::primitive::u8::to_ne_bytes`] (and similar for other integer types)
let impl_8__to_ne_bytes (x: u32) : t_Array u8 (mk_usize 4) = impl_8__to_le_bytes x

/// See [`std::primitive::u8::from_ne_bytes`] (and similar for other integer types)
let impl_8__from_ne_bytes (bytes: t_Array u8 (mk_usize 4)) : u32 = impl_8__from_le_bytes bytes

/// See [`std::primitive::u8::wrapping_shl`] (and similar for other integer types)
let impl_8__wrapping_shl (x n: u32) : u32 = x <<! (n %! impl_8__BITS <: u32)

/// See [`std::primitive::u8::wrapping_shr`] (and similar for other integer types)
let impl_8__wrapping_shr (x n: u32) : u32 = x >>! (n %! impl_8__BITS <: u32)

/// See [`std::primitive::u8::isolate_highest_one`] (and similar for other integer types)
let impl_8__isolate_highest_one (x: u32) : u32 =
  x &.
  (impl_8__wrapping_shr ((impl_8__MAX /! mk_u32 2 <: u32) +! mk_u32 1 <: u32)
      (impl_8__leading_zeros x <: u32)
    <:
    u32)

/// See [`std::primitive::u8::overflowing_shl`] (and similar for other integer types)
let impl_8__overflowing_shl (x n: u32) : (u32 & bool) =
  impl_8__wrapping_shl x n, n >=. impl_8__BITS <: (u32 & bool)

/// See [`std::primitive::u8::overflowing_shr`] (and similar for other integer types)
let impl_8__overflowing_shr (x n: u32) : (u32 & bool) =
  impl_8__wrapping_shr x n, n >=. impl_8__BITS <: (u32 & bool)

/// See [`std::primitive::u8::unbounded_shl`] (and similar for other integer types)
let impl_8__unbounded_shl (x n: u32) : u32 = if n <. impl_8__BITS then x <<! n else mk_u32 0

/// See [`std::primitive::u8::unbounded_shr`] (and similar for other unsigned integer types)
let impl_8__unbounded_shr (x n: u32) : u32 = if n <. impl_8__BITS then x >>! n else mk_u32 0

/// See [`std::primitive::u8::wrapping_next_power_of_two`] (and similar for other unsigned integer types)
let impl_8__wrapping_next_power_of_two (x: u32) : u32 =
  if x <=. mk_u32 1
  then mk_u32 1
  else
    impl_8__wrapping_add (impl_8__MAX >>!
        ((impl_8__leading_zeros (x -! mk_u32 1 <: u32) <: u32) %! impl_8__BITS <: u32)
        <:
        u32)
      (mk_u32 1)

/// See [`std::primitive::u8::reverse_bits`] (and similar for other unsigned integer types)
let impl_8__reverse_bits (x: u32) : u32 =
  let m1:u32 = impl_8__MAX /! mk_u32 3 in
  let m2:u32 = impl_8__MAX /! mk_u32 5 in
  let m4:u32 = impl_8__MAX /! mk_u32 17 in
  let x:u32 =
    (impl_8__wrapping_shl (x &. m1 <: u32) (mk_u32 1) <: u32) |.
    ((impl_8__wrapping_shr x (mk_u32 1) <: u32) &. m1 <: u32)
  in
  let x:u32 =
    (impl_8__wrapping_shl (x &. m2 <: u32) (mk_u32 2) <: u32) |.
    ((impl_8__wrapping_shr x (mk_u32 2) <: u32) &. m2 <: u32)
  in
  let x:u32 =
    (impl_8__wrapping_shl (x &. m4 <: u32) (mk_u32 4) <: u32) |.
    ((impl_8__wrapping_shr x (mk_u32 4) <: u32) &. m4 <: u32)
  in
  impl_8__swap_bytes x

/// See [`std::primitive::u8::widening_mul`] (and similar for other unsigned integer types)
let impl_8__widening_mul (x y: u32) : (u32 & u32) =
  let half:u32 = impl_8__BITS /! mk_u32 2 in
  let lo_mask:u32 = impl_8__wrapping_shr impl_8__MAX half in
  let xl:u32 = x &. lo_mask in
  let xh:u32 = impl_8__wrapping_shr x half in
  let yl:u32 = y &. lo_mask in
  let yh:u32 = impl_8__wrapping_shr y half in
  let ll:u32 = impl_8__wrapping_mul xl yl in
  let lh:u32 = impl_8__wrapping_mul xl yh in
  let hl:u32 = impl_8__wrapping_mul xh yl in
  let hh:u32 = impl_8__wrapping_mul xh yh in
  let mid:u32 =
    impl_8__wrapping_add (impl_8__wrapping_add (impl_8__wrapping_shr ll half <: u32)
          (lh &. lo_mask <: u32)
        <:
        u32)
      (hl &. lo_mask <: u32)
  in
  let low:u32 =
    (ll &. lo_mask <: u32) |. (impl_8__wrapping_shl (mid &. lo_mask <: u32) half <: u32)
  in
  let high:u32 =
    impl_8__wrapping_add (impl_8__wrapping_add (impl_8__wrapping_add hh
              (impl_8__wrapping_shr lh half <: u32)
            <:
            u32)
          (impl_8__wrapping_shr hl half <: u32)
        <:
        u32)
      (impl_8__wrapping_shr mid half <: u32)
  in
  low, high <: (u32 & u32)

/// See [`std::primitive::u8::carrying_mul_add`] (and similar for other unsigned integer types)
let impl_8__carrying_mul_add (x y carry add: u32) : (u32 & u32) =
  let (low: u32), (high: u32) = impl_8__widening_mul x y in
  let (low: u32), (c1: bool) = impl_8__overflowing_add low carry in
  let (low: u32), (c2: bool) = impl_8__overflowing_add low add in
  let high:u32 = impl_8__wrapping_add high (if c1 then mk_u32 1 else mk_u32 0) in
  let high:u32 = impl_8__wrapping_add high (if c2 then mk_u32 1 else mk_u32 0) in
  low, high <: (u32 & u32)

/// See [`std::primitive::u8::carrying_mul`] (and similar for other unsigned integer types)
let impl_8__carrying_mul (x y carry: u32) : (u32 & u32) =
  impl_8__carrying_mul_add x y carry (mk_u32 0)

/// See [`std::primitive::u8::carrying_add`] (and similar for other integer types)
let impl_8__carrying_add (x y: u32) (carry: bool) : (u32 & bool) =
  let (a: u32), (c1: bool) = impl_8__overflowing_add x y in
  let (b: u32), (c2: bool) = impl_8__overflowing_add a (if carry then mk_u32 1 else mk_u32 0) in
  b, c1 || c2 <: (u32 & bool)

/// See [`std::primitive::u8::borrowing_sub`] (and similar for other integer types)
let impl_8__borrowing_sub (x y: u32) (borrow: bool) : (u32 & bool) =
  let (a: u32), (c1: bool) = impl_8__overflowing_sub x y in
  let (b: u32), (c2: bool) = impl_8__overflowing_sub a (if borrow then mk_u32 1 else mk_u32 0) in
  b, c1 || c2 <: (u32 & bool)

/// See [`std::primitive::u8::unchecked_add`] (and similar for other integer types)
let impl_8__unchecked_add (x y: u32)
    : Prims.Pure u32
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_8__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) = x +! y

/// See [`std::primitive::u8::unchecked_sub`] (and similar for other integer types)
let impl_8__unchecked_sub (x y: u32) : Prims.Pure u32 (requires x >=. y) (fun _ -> Prims.l_True) =
  x -! y

/// See [`std::primitive::u8::unchecked_mul`] (and similar for other integer types)
let impl_8__unchecked_mul (x y: u32)
    : Prims.Pure u32
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_8__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) = x *! y

/// See [`std::primitive::u8::rem_euclid`] (and similar for other integer types)
let impl_8__rem_euclid (x y: u32) : Prims.Pure u32 (requires y <>. mk_u32 0) (fun _ -> Prims.l_True) =
  Rust_primitives.Arithmetic.rem_euclid_u32 x y

/// See [`std::primitive::u8::unchecked_div`] (and similar for other integer types)
let impl_8__unchecked_div (x y: u32)
    : Prims.Pure u32 (requires y <>. mk_u32 0) (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::unchecked_rem`] (and similar for other integer types)
let impl_8__unchecked_rem (x y: u32)
    : Prims.Pure u32 (requires y <>. mk_u32 0) (fun _ -> Prims.l_True) = x %! y

/// See [`std::primitive::u8::div_ceil`] (and similar for other unsigned integer types)
let impl_8__div_ceil (x y: u32) : Prims.Pure u32 (requires y <>. mk_u32 0) (fun _ -> Prims.l_True) =
  let d:u32 = x /! y in
  let r:u32 = x %! y in
  if r >. mk_u32 0 then d +! mk_u32 1 else d

/// See [`std::primitive::u8::strict_neg`] (and similar for other integer types)
let impl_8__strict_neg (x: u32) : Prims.Pure u32 (requires x =. mk_u32 0) (fun _ -> Prims.l_True) =
  if x =. mk_u32 0 then mk_u32 0 else Core_models.Panicking.Internal.panic #u32 ()

/// See [`std::primitive::u8::strict_pow`] (and similar for other integer types)
let impl_8__strict_pow (x exp: u32)
    : Prims.Pure u32
      (requires (impl_8__overflowing_pow x exp <: (u32 & bool))._2 =. false)
      (fun _ -> Prims.l_True) =
  let (result: u32), (overflowed: bool) = impl_8__overflowing_pow x exp in
  if overflowed then Core_models.Panicking.Internal.panic #u32 () else result

/// See [`std::primitive::u8::strict_add`] (and similar for other integer types)
let impl_8__strict_add (x y: u32)
    : Prims.Pure u32
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_8__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: u32), (overflowed: bool) = impl_8__overflowing_add x y in
  if overflowed then Core_models.Panicking.Internal.panic #u32 () else result

/// See [`std::primitive::u8::strict_sub`] (and similar for other integer types)
let impl_8__strict_sub (x y: u32) : Prims.Pure u32 (requires x >=. y) (fun _ -> Prims.l_True) =
  let (result: u32), (overflowed: bool) = impl_8__overflowing_sub x y in
  if overflowed then Core_models.Panicking.Internal.panic #u32 () else result

/// See [`std::primitive::u8::strict_mul`] (and similar for other integer types)
let impl_8__strict_mul (x y: u32)
    : Prims.Pure u32
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_8__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: u32), (overflowed: bool) = impl_8__overflowing_mul x y in
  if overflowed then Core_models.Panicking.Internal.panic #u32 () else result

/// See [`std::primitive::u8::wrapping_div`] (and similar for other unsigned integer types)
let impl_8__wrapping_div (x y: u32)
    : Prims.Pure u32 (requires y <>. mk_u32 0) (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::wrapping_rem`] (and similar for other unsigned integer types)
let impl_8__wrapping_rem (x y: u32)
    : Prims.Pure u32 (requires y <>. mk_u32 0) (fun _ -> Prims.l_True) = x %! y

/// See [`std::primitive::u8::wrapping_div_euclid`] (and similar for other unsigned integer types)
let impl_8__wrapping_div_euclid (x y: u32)
    : Prims.Pure u32 (requires y <>. mk_u32 0) (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::wrapping_rem_euclid`] (and similar for other unsigned integer types)
let impl_8__wrapping_rem_euclid (x y: u32)
    : Prims.Pure u32 (requires y <>. mk_u32 0) (fun _ -> Prims.l_True) = x %! y

/// See [`std::primitive::u8::saturating_div`] (and similar for other unsigned integer types)
let impl_8__saturating_div (x y: u32)
    : Prims.Pure u32 (requires y <>. mk_u32 0) (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::strict_div`] (and similar for other unsigned integer types)
let impl_8__strict_div (x y: u32) : Prims.Pure u32 (requires y <>. mk_u32 0) (fun _ -> Prims.l_True) =
  x /! y

/// See [`std::primitive::u8::strict_rem`] (and similar for other unsigned integer types)
let impl_8__strict_rem (x y: u32) : Prims.Pure u32 (requires y <>. mk_u32 0) (fun _ -> Prims.l_True) =
  x %! y

/// See [`std::primitive::u8::strict_div_euclid`] (and similar for other unsigned integer types)
let impl_8__strict_div_euclid (x y: u32)
    : Prims.Pure u32 (requires y <>. mk_u32 0) (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::strict_rem_euclid`] (and similar for other unsigned integer types)
let impl_8__strict_rem_euclid (x y: u32)
    : Prims.Pure u32 (requires y <>. mk_u32 0) (fun _ -> Prims.l_True) = x %! y

/// See [`std::primitive::u8::div_euclid`] (and similar for other unsigned integer types)
let impl_8__div_euclid (x y: u32) : Prims.Pure u32 (requires y <>. mk_u32 0) (fun _ -> Prims.l_True) =
  x /! y

/// See [`std::primitive::u8::div_floor`] (and similar for other unsigned integer types)
let impl_8__div_floor (x y: u32) : Prims.Pure u32 (requires y <>. mk_u32 0) (fun _ -> Prims.l_True) =
  x /! y

/// See [`std::primitive::u8::overflowing_div`] (and similar for other unsigned integer types)
let impl_8__overflowing_div (x y: u32)
    : Prims.Pure (u32 & bool) (requires y <>. mk_u32 0) (fun _ -> Prims.l_True) =
  x /! y, false <: (u32 & bool)

/// See [`std::primitive::u8::overflowing_rem`] (and similar for other unsigned integer types)
let impl_8__overflowing_rem (x y: u32)
    : Prims.Pure (u32 & bool) (requires y <>. mk_u32 0) (fun _ -> Prims.l_True) =
  x %! y, false <: (u32 & bool)

/// See [`std::primitive::u8::overflowing_div_euclid`] (and similar for other unsigned integer types)
let impl_8__overflowing_div_euclid (x y: u32)
    : Prims.Pure (u32 & bool) (requires y <>. mk_u32 0) (fun _ -> Prims.l_True) =
  x /! y, false <: (u32 & bool)

/// See [`std::primitive::u8::overflowing_rem_euclid`] (and similar for other unsigned integer types)
let impl_8__overflowing_rem_euclid (x y: u32)
    : Prims.Pure (u32 & bool) (requires y <>. mk_u32 0) (fun _ -> Prims.l_True) =
  x %! y, false <: (u32 & bool)

/// See [`std::primitive::u8::unchecked_div_exact`] (and similar for other unsigned integer types)
let impl_8__unchecked_div_exact (x y: u32)
    : Prims.Pure u32
      (requires y <>. mk_u32 0 && (x %! y <: u32) =. mk_u32 0)
      (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::next_multiple_of`] (and similar for other unsigned integer types)
let impl_8__next_multiple_of (x y: u32)
    : Prims.Pure u32
      (requires
        y <>. mk_u32 0 &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine ((y -! (x %! y <: u32) <: u32) %! y <: u32)
            <:
            Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_8__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) = x +! ((y -! (x %! y <: u32) <: u32) %! y <: u32)

/// See [`std::primitive::u8::strict_add_signed`] (and similar for other unsigned integer types)
let impl_8__strict_add_signed (x: u32) (y: i32)
    : Prims.Pure u32
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_8__MIN <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_8__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: u32), (overflowed: bool) = impl_8__overflowing_add_signed x y in
  if overflowed then Core_models.Panicking.Internal.panic #u32 () else result

/// See [`std::primitive::u8::strict_sub_signed`] (and similar for other unsigned integer types)
let impl_8__strict_sub_signed (x: u32) (y: i32)
    : Prims.Pure u32
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_8__MIN <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_8__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: u32), (overflowed: bool) = impl_8__overflowing_sub_signed x y in
  if overflowed then Core_models.Panicking.Internal.panic #u32 () else result

/// See [`std::primitive::u8::strict_shl`] (and similar for other integer types)
let impl_8__strict_shl (x n: u32)
    : Prims.Pure u32 (requires n <. impl_8__BITS) (fun _ -> Prims.l_True) =
  if n <. impl_8__BITS then x <<! n else Core_models.Panicking.Internal.panic #u32 ()

/// See [`std::primitive::u8::strict_shr`] (and similar for other integer types)
let impl_8__strict_shr (x n: u32)
    : Prims.Pure u32 (requires n <. impl_8__BITS) (fun _ -> Prims.l_True) =
  if n <. impl_8__BITS then x >>! n else Core_models.Panicking.Internal.panic #u32 ()

/// See [`std::primitive::u8::unchecked_shl`] (and similar for other integer types)
let impl_8__unchecked_shl (x n: u32)
    : Prims.Pure u32 (requires n <. impl_8__BITS) (fun _ -> Prims.l_True) = x <<! n

/// See [`std::primitive::u8::unchecked_shr`] (and similar for other integer types)
let impl_8__unchecked_shr (x n: u32)
    : Prims.Pure u32 (requires n <. impl_8__BITS) (fun _ -> Prims.l_True) = x >>! n

/// See [`std::primitive::u8::unchecked_shl_exact`] (and similar for other unsigned integer types)
let impl_8__unchecked_shl_exact (x n: u32)
    : Prims.Pure u32
      (requires n <=. (impl_8__leading_zeros x <: u32) && n <. impl_8__BITS)
      (fun _ -> Prims.l_True) = x <<! n

/// See [`std::primitive::u8::unchecked_shr_exact`] (and similar for other integer types)
let impl_8__unchecked_shr_exact (x n: u32)
    : Prims.Pure u32
      (requires n <=. (impl_8__trailing_zeros x <: u32) && n <. impl_8__BITS)
      (fun _ -> Prims.l_True) = x >>! n

/// See [`std::primitive::u8::funnel_shl`] (and similar for other unsigned integer types)
let impl_8__funnel_shl (x y n: u32)
    : Prims.Pure u32 (requires n <. impl_8__BITS) (fun _ -> Prims.l_True) =
  if n =. mk_u32 0
  then x
  else
    (impl_8__wrapping_shl x n <: u32) |. (impl_8__wrapping_shr y (impl_8__BITS -! n <: u32) <: u32)

/// See [`std::primitive::u8::funnel_shr`] (and similar for other unsigned integer types)
let impl_8__funnel_shr (x y n: u32)
    : Prims.Pure u32 (requires n <. impl_8__BITS) (fun _ -> Prims.l_True) =
  if n =. mk_u32 0
  then y
  else
    (impl_8__wrapping_shr y n <: u32) |. (impl_8__wrapping_shl x (impl_8__BITS -! n <: u32) <: u32)

/// See [`std::primitive::u8::unchecked_disjoint_bitor`] (and similar for other unsigned integer types)
let impl_8__unchecked_disjoint_bitor (x y: u32)
    : Prims.Pure u32 (requires (x &. y <: u32) =. mk_u32 0) (fun _ -> Prims.l_True) = x |. y

/// See [`std::primitive::u8::next_power_of_two`] (and similar for other unsigned integer types)
assume
val impl_8__next_power_of_two': x: u32
  -> Prims.Pure u32
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine (mk_i32 2) <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        ((Rust_primitives.Hax.Int.from_machine impl_8__MAX <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine (mk_i32 1) <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True)

unfold
let impl_8__next_power_of_two = impl_8__next_power_of_two'

/// See [`std::primitive::u8::MIN`] (and similar for other unsigned integer types)
let impl_9__MIN: u64 = mk_u64 0

/// See [`std::primitive::u8::MAX`] (and similar for other unsigned integer types)
let impl_9__MAX: u64 = mk_u64 18446744073709551615

/// See [`std::primitive::u8::BITS`] (and similar for other unsigned integer types)
let impl_9__BITS: u32 = mk_u32 64

/// See [`std::primitive::u8::wrapping_add`] (and similar for other unsigned integer types)
let impl_9__wrapping_add (x y: u64) : u64 = Rust_primitives.Arithmetic.wrapping_add_u64 x y

/// See [`std::primitive::u8::saturating_add`] (and similar for other integer types)
let impl_9__saturating_add (x y: u64) : u64 = Rust_primitives.Arithmetic.saturating_add_u64 x y

/// See [`std::primitive::u8::overflowing_add`] (and similar for other integer types)
let impl_9__overflowing_add (x y: u64) : (u64 & bool) =
  Rust_primitives.Arithmetic.overflowing_add_u64 x y

/// See [`std::primitive::u8::wrapping_sub`] (and similar for other integer types)
let impl_9__wrapping_sub (x y: u64) : u64 = Rust_primitives.Arithmetic.wrapping_sub_u64 x y

/// See [`std::primitive::u8::saturating_sub`] (and similar for other integer types)
let impl_9__saturating_sub (x y: u64) : u64 = Rust_primitives.Arithmetic.saturating_sub_u64 x y

/// See [`std::primitive::u8::overflowing_sub`] (and similar for other integer types)
let impl_9__overflowing_sub (x y: u64) : (u64 & bool) =
  Rust_primitives.Arithmetic.overflowing_sub_u64 x y

/// See [`std::primitive::u8::wrapping_mul`] (and similar for other integer types)
let impl_9__wrapping_mul (x y: u64) : u64 = Rust_primitives.Arithmetic.wrapping_mul_u64 x y

/// See [`std::primitive::u8::saturating_mul`] (and similar for other integer types)
let impl_9__saturating_mul (x y: u64) : u64 = Rust_primitives.Arithmetic.saturating_mul_u64 x y

/// See [`std::primitive::u8::overflowing_mul`] (and similar for other integer types)
let impl_9__overflowing_mul (x y: u64) : (u64 & bool) =
  Rust_primitives.Arithmetic.overflowing_mul_u64 x y

/// See [`std::primitive::u8::pow`] (and similar for other integer types)
let impl_9__pow (x: u64) (exp: u32) : u64 = Rust_primitives.Arithmetic.pow_u64 x exp

/// See [`std::primitive::u8::overflowing_pow`] (and similar for other integer types)
let impl_9__overflowing_pow (x: u64) (exp: u32) : (u64 & bool) =
  Rust_primitives.Arithmetic.overflowing_pow_u64 x exp

/// See [`std::primitive::u8::count_ones`] (and similar for other integer types)
let impl_9__count_ones (x: u64) : u32 = Rust_primitives.Arithmetic.count_ones_u64 x

/// See [`std::primitive::u8::rotate_right`] (and similar for other integer types)
assume
val impl_9__rotate_right': x: u64 -> n: u32 -> u64

unfold
let impl_9__rotate_right = impl_9__rotate_right'

/// See [`std::primitive::u8::rotate_left`] (and similar for other integer types)
assume
val impl_9__rotate_left': x: u64 -> n: u32 -> u64

unfold
let impl_9__rotate_left = impl_9__rotate_left'

/// See [`std::primitive::u8::leading_zeros`] (and similar for other integer types)
assume
val impl_9__leading_zeros': x: u64 -> u32

unfold
let impl_9__leading_zeros = impl_9__leading_zeros'

/// See [`std::primitive::u8::ilog2`] (and similar for other integer types)
assume
val impl_9__ilog2': x: u64 -> u32

unfold
let impl_9__ilog2 = impl_9__ilog2'

/// See [`std::primitive::u8::from_be_bytes`] (and similar for other integer types)
assume
val impl_9__from_be_bytes': bytes: t_Array u8 (mk_usize 8) -> u64

unfold
let impl_9__from_be_bytes = impl_9__from_be_bytes'

/// See [`std::primitive::u8::from_le_bytes`] (and similar for other integer types)
assume
val impl_9__from_le_bytes': bytes: t_Array u8 (mk_usize 8) -> u64

unfold
let impl_9__from_le_bytes = impl_9__from_le_bytes'

/// See [`std::primitive::u8::to_be_bytes`] (and similar for other integer types)
assume
val impl_9__to_be_bytes': bytes: u64 -> t_Array u8 (mk_usize 8)

unfold
let impl_9__to_be_bytes = impl_9__to_be_bytes'

/// See [`std::primitive::u8::to_le_bytes`] (and similar for other integer types)
assume
val impl_9__to_le_bytes': bytes: u64 -> t_Array u8 (mk_usize 8)

unfold
let impl_9__to_le_bytes = impl_9__to_le_bytes'

/// See [`std::primitive::u8::is_power_of_two`] (and similar for other unsigned integer types)
let impl_9__is_power_of_two (x: u64) : bool =
  x <>. mk_u64 0 && (x &. (x -! mk_u64 1 <: u64) <: u64) =. mk_u64 0

/// See [`std::primitive::u8::is_multiple_of`] (and similar for other unsigned integer types)
let impl_9__is_multiple_of (x y: u64) : bool =
  if y =. mk_u64 0 then x =. mk_u64 0 else (x %! y <: u64) =. mk_u64 0

/// See [`std::primitive::u8::wrapping_neg`] (and similar for other integer types)
let impl_9__wrapping_neg (x: u64) : u64 = Rust_primitives.Arithmetic.wrapping_sub_u64 (mk_u64 0) x

/// See [`std::primitive::u8::min_value`] (and similar for other integer types)
let impl_9__min_value (_: Prims.unit) : u64 = impl_9__MIN

/// See [`std::primitive::u8::max_value`] (and similar for other integer types)
let impl_9__max_value (_: Prims.unit) : u64 = impl_9__MAX

/// See [`std::primitive::u8::cast_signed`] (and similar for other unsigned integer types)
let impl_9__cast_signed (x: u64) : i64 = cast (x <: u64) <: i64

/// See [`std::primitive::u8::count_zeros`] (and similar for other integer types)
let impl_9__count_zeros (x: u64) : u32 = impl_9__BITS -! (impl_9__count_ones x <: u32)

/// See [`std::primitive::u8::overflowing_neg`] (and similar for other integer types)
let impl_9__overflowing_neg (x: u64) : (u64 & bool) =
  impl_9__wrapping_neg x, x <>. mk_u64 0 <: (u64 & bool)

/// See [`std::primitive::u8::wrapping_pow`] (and similar for other integer types)
let impl_9__wrapping_pow (x: u64) (exp: u32) : u64 =
  let (result: u64), (_: bool) = impl_9__overflowing_pow x exp in
  result

/// See [`std::primitive::u8::saturating_pow`] (and similar for other unsigned integer types)
let impl_9__saturating_pow (x: u64) (exp: u32) : u64 =
  let (result: u64), (overflowed: bool) = impl_9__overflowing_pow x exp in
  if overflowed then impl_9__MAX else result

/// See [`std::primitive::u8::abs_diff`] (and similar for other unsigned integer types)
let impl_9__abs_diff (x y: u64) : u64 = if x <. y then y -! x else x -! y

/// See [`std::primitive::u8::midpoint`] (and similar for other unsigned integer types)
let impl_9__midpoint (x y: u64) : u64 =
  impl_9__wrapping_add ((x ^. y <: u64) >>! mk_i32 1 <: u64) (x &. y <: u64)

/// See [`std::primitive::u8::wrapping_add_signed`] (and similar for other unsigned integer types)
let impl_9__wrapping_add_signed (x: u64) (y: i64) : u64 =
  impl_9__wrapping_add x (cast (y <: i64) <: u64)

/// See [`std::primitive::u8::wrapping_sub_signed`] (and similar for other unsigned integer types)
let impl_9__wrapping_sub_signed (x: u64) (y: i64) : u64 =
  impl_9__wrapping_sub x (cast (y <: i64) <: u64)

/// See [`std::primitive::u8::overflowing_add_signed`] (and similar for other unsigned integer types)
let impl_9__overflowing_add_signed (x: u64) (y: i64) : (u64 & bool) =
  let (result: u64), (overflowed: bool) = impl_9__overflowing_add x (cast (y <: i64) <: u64) in
  result, overflowed <>. (y <. mk_i64 0 <: bool) <: (u64 & bool)

/// See [`std::primitive::u8::overflowing_sub_signed`] (and similar for other unsigned integer types)
let impl_9__overflowing_sub_signed (x: u64) (y: i64) : (u64 & bool) =
  let (result: u64), (overflowed: bool) = impl_9__overflowing_sub x (cast (y <: i64) <: u64) in
  result, overflowed <>. (y <. mk_i64 0 <: bool) <: (u64 & bool)

/// See [`std::primitive::u8::saturating_add_signed`] (and similar for other unsigned integer types)
let impl_9__saturating_add_signed (x: u64) (y: i64) : u64 =
  let (result: u64), (overflowed: bool) = impl_9__overflowing_add_signed x y in
  if ~.overflowed then result else if y <. mk_i64 0 then impl_9__MIN else impl_9__MAX

/// See [`std::primitive::u8::saturating_sub_signed`] (and similar for other unsigned integer types)
let impl_9__saturating_sub_signed (x: u64) (y: i64) : u64 =
  let (result: u64), (overflowed: bool) = impl_9__overflowing_sub_signed x y in
  if ~.overflowed then result else if y <. mk_i64 0 then impl_9__MAX else impl_9__MIN

/// See [`std::primitive::u8::trailing_zeros`] (and similar for other integer types)
let impl_9__trailing_zeros (x: u64) : u32 =
  if x =. mk_u64 0
  then impl_9__BITS
  else
    impl_9__count_ones (impl_9__wrapping_sub (x &. (impl_9__wrapping_neg x <: u64) <: u64)
          (mk_u64 1)
        <:
        u64)

/// See [`std::primitive::u8::trailing_ones`] (and similar for other integer types)
let impl_9__trailing_ones (x: u64) : u32 =
  impl_9__trailing_zeros (impl_9__wrapping_sub impl_9__MAX x <: u64)

/// See [`std::primitive::u8::leading_ones`] (and similar for other integer types)
let impl_9__leading_ones (x: u64) : u32 =
  impl_9__leading_zeros (impl_9__wrapping_sub impl_9__MAX x <: u64)

/// See [`std::primitive::u8::bit_width`] (and similar for other unsigned integer types)
assume
val impl_9__bit_width': x: u64 -> u32

unfold
let impl_9__bit_width = impl_9__bit_width'

/// See [`std::primitive::u8::isolate_lowest_one`] (and similar for other integer types)
let impl_9__isolate_lowest_one (x: u64) : u64 = x &. (impl_9__wrapping_neg x <: u64)

/// See [`std::primitive::u8::swap_bytes`] (and similar for other integer types)
let impl_9__swap_bytes (x: u64) : u64 =
  impl_9__from_le_bytes (impl_9__to_be_bytes x <: t_Array u8 (mk_usize 8))

/// See [`std::primitive::u8::to_be`] (and similar for other integer types)
let impl_9__to_be (x: u64) : u64 = impl_9__swap_bytes x

/// See [`std::primitive::u8::to_le`] (and similar for other integer types)
let impl_9__to_le (x: u64) : u64 = x

/// See [`std::primitive::u8::from_be`] (and similar for other integer types)
let impl_9__from_be (x: u64) : u64 = impl_9__swap_bytes x

/// See [`std::primitive::u8::from_le`] (and similar for other integer types)
let impl_9__from_le (x: u64) : u64 = x

/// See [`std::primitive::u8::to_ne_bytes`] (and similar for other integer types)
let impl_9__to_ne_bytes (x: u64) : t_Array u8 (mk_usize 8) = impl_9__to_le_bytes x

/// See [`std::primitive::u8::from_ne_bytes`] (and similar for other integer types)
let impl_9__from_ne_bytes (bytes: t_Array u8 (mk_usize 8)) : u64 = impl_9__from_le_bytes bytes

/// See [`std::primitive::u8::wrapping_shl`] (and similar for other integer types)
let impl_9__wrapping_shl (x: u64) (n: u32) : u64 = x <<! (n %! impl_9__BITS <: u32)

/// See [`std::primitive::u8::wrapping_shr`] (and similar for other integer types)
let impl_9__wrapping_shr (x: u64) (n: u32) : u64 = x >>! (n %! impl_9__BITS <: u32)

/// See [`std::primitive::u8::isolate_highest_one`] (and similar for other integer types)
let impl_9__isolate_highest_one (x: u64) : u64 =
  x &.
  (impl_9__wrapping_shr ((impl_9__MAX /! mk_u64 2 <: u64) +! mk_u64 1 <: u64)
      (impl_9__leading_zeros x <: u32)
    <:
    u64)

/// See [`std::primitive::u8::overflowing_shl`] (and similar for other integer types)
let impl_9__overflowing_shl (x: u64) (n: u32) : (u64 & bool) =
  impl_9__wrapping_shl x n, n >=. impl_9__BITS <: (u64 & bool)

/// See [`std::primitive::u8::overflowing_shr`] (and similar for other integer types)
let impl_9__overflowing_shr (x: u64) (n: u32) : (u64 & bool) =
  impl_9__wrapping_shr x n, n >=. impl_9__BITS <: (u64 & bool)

/// See [`std::primitive::u8::unbounded_shl`] (and similar for other integer types)
let impl_9__unbounded_shl (x: u64) (n: u32) : u64 = if n <. impl_9__BITS then x <<! n else mk_u64 0

/// See [`std::primitive::u8::unbounded_shr`] (and similar for other unsigned integer types)
let impl_9__unbounded_shr (x: u64) (n: u32) : u64 = if n <. impl_9__BITS then x >>! n else mk_u64 0

/// See [`std::primitive::u8::wrapping_next_power_of_two`] (and similar for other unsigned integer types)
let impl_9__wrapping_next_power_of_two (x: u64) : u64 =
  if x <=. mk_u64 1
  then mk_u64 1
  else
    impl_9__wrapping_add (impl_9__MAX >>!
        ((impl_9__leading_zeros (x -! mk_u64 1 <: u64) <: u32) %! impl_9__BITS <: u32)
        <:
        u64)
      (mk_u64 1)

/// See [`std::primitive::u8::reverse_bits`] (and similar for other unsigned integer types)
let impl_9__reverse_bits (x: u64) : u64 =
  let m1:u64 = impl_9__MAX /! mk_u64 3 in
  let m2:u64 = impl_9__MAX /! mk_u64 5 in
  let m4:u64 = impl_9__MAX /! mk_u64 17 in
  let x:u64 =
    (impl_9__wrapping_shl (x &. m1 <: u64) (mk_u32 1) <: u64) |.
    ((impl_9__wrapping_shr x (mk_u32 1) <: u64) &. m1 <: u64)
  in
  let x:u64 =
    (impl_9__wrapping_shl (x &. m2 <: u64) (mk_u32 2) <: u64) |.
    ((impl_9__wrapping_shr x (mk_u32 2) <: u64) &. m2 <: u64)
  in
  let x:u64 =
    (impl_9__wrapping_shl (x &. m4 <: u64) (mk_u32 4) <: u64) |.
    ((impl_9__wrapping_shr x (mk_u32 4) <: u64) &. m4 <: u64)
  in
  impl_9__swap_bytes x

/// See [`std::primitive::u8::widening_mul`] (and similar for other unsigned integer types)
let impl_9__widening_mul (x y: u64) : (u64 & u64) =
  let half:u32 = impl_9__BITS /! mk_u32 2 in
  let lo_mask:u64 = impl_9__wrapping_shr impl_9__MAX half in
  let xl:u64 = x &. lo_mask in
  let xh:u64 = impl_9__wrapping_shr x half in
  let yl:u64 = y &. lo_mask in
  let yh:u64 = impl_9__wrapping_shr y half in
  let ll:u64 = impl_9__wrapping_mul xl yl in
  let lh:u64 = impl_9__wrapping_mul xl yh in
  let hl:u64 = impl_9__wrapping_mul xh yl in
  let hh:u64 = impl_9__wrapping_mul xh yh in
  let mid:u64 =
    impl_9__wrapping_add (impl_9__wrapping_add (impl_9__wrapping_shr ll half <: u64)
          (lh &. lo_mask <: u64)
        <:
        u64)
      (hl &. lo_mask <: u64)
  in
  let low:u64 =
    (ll &. lo_mask <: u64) |. (impl_9__wrapping_shl (mid &. lo_mask <: u64) half <: u64)
  in
  let high:u64 =
    impl_9__wrapping_add (impl_9__wrapping_add (impl_9__wrapping_add hh
              (impl_9__wrapping_shr lh half <: u64)
            <:
            u64)
          (impl_9__wrapping_shr hl half <: u64)
        <:
        u64)
      (impl_9__wrapping_shr mid half <: u64)
  in
  low, high <: (u64 & u64)

/// See [`std::primitive::u8::carrying_mul_add`] (and similar for other unsigned integer types)
let impl_9__carrying_mul_add (x y carry add: u64) : (u64 & u64) =
  let (low: u64), (high: u64) = impl_9__widening_mul x y in
  let (low: u64), (c1: bool) = impl_9__overflowing_add low carry in
  let (low: u64), (c2: bool) = impl_9__overflowing_add low add in
  let high:u64 = impl_9__wrapping_add high (if c1 then mk_u64 1 else mk_u64 0) in
  let high:u64 = impl_9__wrapping_add high (if c2 then mk_u64 1 else mk_u64 0) in
  low, high <: (u64 & u64)

/// See [`std::primitive::u8::carrying_mul`] (and similar for other unsigned integer types)
let impl_9__carrying_mul (x y carry: u64) : (u64 & u64) =
  impl_9__carrying_mul_add x y carry (mk_u64 0)

/// See [`std::primitive::u8::carrying_add`] (and similar for other integer types)
let impl_9__carrying_add (x y: u64) (carry: bool) : (u64 & bool) =
  let (a: u64), (c1: bool) = impl_9__overflowing_add x y in
  let (b: u64), (c2: bool) = impl_9__overflowing_add a (if carry then mk_u64 1 else mk_u64 0) in
  b, c1 || c2 <: (u64 & bool)

/// See [`std::primitive::u8::borrowing_sub`] (and similar for other integer types)
let impl_9__borrowing_sub (x y: u64) (borrow: bool) : (u64 & bool) =
  let (a: u64), (c1: bool) = impl_9__overflowing_sub x y in
  let (b: u64), (c2: bool) = impl_9__overflowing_sub a (if borrow then mk_u64 1 else mk_u64 0) in
  b, c1 || c2 <: (u64 & bool)

/// See [`std::primitive::u8::unchecked_add`] (and similar for other integer types)
let impl_9__unchecked_add (x y: u64)
    : Prims.Pure u64
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_9__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) = x +! y

/// See [`std::primitive::u8::unchecked_sub`] (and similar for other integer types)
let impl_9__unchecked_sub (x y: u64) : Prims.Pure u64 (requires x >=. y) (fun _ -> Prims.l_True) =
  x -! y

/// See [`std::primitive::u8::unchecked_mul`] (and similar for other integer types)
let impl_9__unchecked_mul (x y: u64)
    : Prims.Pure u64
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_9__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) = x *! y

/// See [`std::primitive::u8::rem_euclid`] (and similar for other integer types)
let impl_9__rem_euclid (x y: u64) : Prims.Pure u64 (requires y <>. mk_u64 0) (fun _ -> Prims.l_True) =
  Rust_primitives.Arithmetic.rem_euclid_u64 x y

/// See [`std::primitive::u8::unchecked_div`] (and similar for other integer types)
let impl_9__unchecked_div (x y: u64)
    : Prims.Pure u64 (requires y <>. mk_u64 0) (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::unchecked_rem`] (and similar for other integer types)
let impl_9__unchecked_rem (x y: u64)
    : Prims.Pure u64 (requires y <>. mk_u64 0) (fun _ -> Prims.l_True) = x %! y

/// See [`std::primitive::u8::div_ceil`] (and similar for other unsigned integer types)
let impl_9__div_ceil (x y: u64) : Prims.Pure u64 (requires y <>. mk_u64 0) (fun _ -> Prims.l_True) =
  let d:u64 = x /! y in
  let r:u64 = x %! y in
  if r >. mk_u64 0 then d +! mk_u64 1 else d

/// See [`std::primitive::u8::strict_neg`] (and similar for other integer types)
let impl_9__strict_neg (x: u64) : Prims.Pure u64 (requires x =. mk_u64 0) (fun _ -> Prims.l_True) =
  if x =. mk_u64 0 then mk_u64 0 else Core_models.Panicking.Internal.panic #u64 ()

/// See [`std::primitive::u8::strict_pow`] (and similar for other integer types)
let impl_9__strict_pow (x: u64) (exp: u32)
    : Prims.Pure u64
      (requires (impl_9__overflowing_pow x exp <: (u64 & bool))._2 =. false)
      (fun _ -> Prims.l_True) =
  let (result: u64), (overflowed: bool) = impl_9__overflowing_pow x exp in
  if overflowed then Core_models.Panicking.Internal.panic #u64 () else result

/// See [`std::primitive::u8::strict_add`] (and similar for other integer types)
let impl_9__strict_add (x y: u64)
    : Prims.Pure u64
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_9__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: u64), (overflowed: bool) = impl_9__overflowing_add x y in
  if overflowed then Core_models.Panicking.Internal.panic #u64 () else result

/// See [`std::primitive::u8::strict_sub`] (and similar for other integer types)
let impl_9__strict_sub (x y: u64) : Prims.Pure u64 (requires x >=. y) (fun _ -> Prims.l_True) =
  let (result: u64), (overflowed: bool) = impl_9__overflowing_sub x y in
  if overflowed then Core_models.Panicking.Internal.panic #u64 () else result

/// See [`std::primitive::u8::strict_mul`] (and similar for other integer types)
let impl_9__strict_mul (x y: u64)
    : Prims.Pure u64
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_9__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: u64), (overflowed: bool) = impl_9__overflowing_mul x y in
  if overflowed then Core_models.Panicking.Internal.panic #u64 () else result

/// See [`std::primitive::u8::wrapping_div`] (and similar for other unsigned integer types)
let impl_9__wrapping_div (x y: u64)
    : Prims.Pure u64 (requires y <>. mk_u64 0) (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::wrapping_rem`] (and similar for other unsigned integer types)
let impl_9__wrapping_rem (x y: u64)
    : Prims.Pure u64 (requires y <>. mk_u64 0) (fun _ -> Prims.l_True) = x %! y

/// See [`std::primitive::u8::wrapping_div_euclid`] (and similar for other unsigned integer types)
let impl_9__wrapping_div_euclid (x y: u64)
    : Prims.Pure u64 (requires y <>. mk_u64 0) (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::wrapping_rem_euclid`] (and similar for other unsigned integer types)
let impl_9__wrapping_rem_euclid (x y: u64)
    : Prims.Pure u64 (requires y <>. mk_u64 0) (fun _ -> Prims.l_True) = x %! y

/// See [`std::primitive::u8::saturating_div`] (and similar for other unsigned integer types)
let impl_9__saturating_div (x y: u64)
    : Prims.Pure u64 (requires y <>. mk_u64 0) (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::strict_div`] (and similar for other unsigned integer types)
let impl_9__strict_div (x y: u64) : Prims.Pure u64 (requires y <>. mk_u64 0) (fun _ -> Prims.l_True) =
  x /! y

/// See [`std::primitive::u8::strict_rem`] (and similar for other unsigned integer types)
let impl_9__strict_rem (x y: u64) : Prims.Pure u64 (requires y <>. mk_u64 0) (fun _ -> Prims.l_True) =
  x %! y

/// See [`std::primitive::u8::strict_div_euclid`] (and similar for other unsigned integer types)
let impl_9__strict_div_euclid (x y: u64)
    : Prims.Pure u64 (requires y <>. mk_u64 0) (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::strict_rem_euclid`] (and similar for other unsigned integer types)
let impl_9__strict_rem_euclid (x y: u64)
    : Prims.Pure u64 (requires y <>. mk_u64 0) (fun _ -> Prims.l_True) = x %! y

/// See [`std::primitive::u8::div_euclid`] (and similar for other unsigned integer types)
let impl_9__div_euclid (x y: u64) : Prims.Pure u64 (requires y <>. mk_u64 0) (fun _ -> Prims.l_True) =
  x /! y

/// See [`std::primitive::u8::div_floor`] (and similar for other unsigned integer types)
let impl_9__div_floor (x y: u64) : Prims.Pure u64 (requires y <>. mk_u64 0) (fun _ -> Prims.l_True) =
  x /! y

/// See [`std::primitive::u8::overflowing_div`] (and similar for other unsigned integer types)
let impl_9__overflowing_div (x y: u64)
    : Prims.Pure (u64 & bool) (requires y <>. mk_u64 0) (fun _ -> Prims.l_True) =
  x /! y, false <: (u64 & bool)

/// See [`std::primitive::u8::overflowing_rem`] (and similar for other unsigned integer types)
let impl_9__overflowing_rem (x y: u64)
    : Prims.Pure (u64 & bool) (requires y <>. mk_u64 0) (fun _ -> Prims.l_True) =
  x %! y, false <: (u64 & bool)

/// See [`std::primitive::u8::overflowing_div_euclid`] (and similar for other unsigned integer types)
let impl_9__overflowing_div_euclid (x y: u64)
    : Prims.Pure (u64 & bool) (requires y <>. mk_u64 0) (fun _ -> Prims.l_True) =
  x /! y, false <: (u64 & bool)

/// See [`std::primitive::u8::overflowing_rem_euclid`] (and similar for other unsigned integer types)
let impl_9__overflowing_rem_euclid (x y: u64)
    : Prims.Pure (u64 & bool) (requires y <>. mk_u64 0) (fun _ -> Prims.l_True) =
  x %! y, false <: (u64 & bool)

/// See [`std::primitive::u8::unchecked_div_exact`] (and similar for other unsigned integer types)
let impl_9__unchecked_div_exact (x y: u64)
    : Prims.Pure u64
      (requires y <>. mk_u64 0 && (x %! y <: u64) =. mk_u64 0)
      (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::next_multiple_of`] (and similar for other unsigned integer types)
let impl_9__next_multiple_of (x y: u64)
    : Prims.Pure u64
      (requires
        y <>. mk_u64 0 &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine ((y -! (x %! y <: u64) <: u64) %! y <: u64)
            <:
            Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_9__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) = x +! ((y -! (x %! y <: u64) <: u64) %! y <: u64)

/// See [`std::primitive::u8::strict_add_signed`] (and similar for other unsigned integer types)
let impl_9__strict_add_signed (x: u64) (y: i64)
    : Prims.Pure u64
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_9__MIN <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_9__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: u64), (overflowed: bool) = impl_9__overflowing_add_signed x y in
  if overflowed then Core_models.Panicking.Internal.panic #u64 () else result

/// See [`std::primitive::u8::strict_sub_signed`] (and similar for other unsigned integer types)
let impl_9__strict_sub_signed (x: u64) (y: i64)
    : Prims.Pure u64
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_9__MIN <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_9__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: u64), (overflowed: bool) = impl_9__overflowing_sub_signed x y in
  if overflowed then Core_models.Panicking.Internal.panic #u64 () else result

/// See [`std::primitive::u8::strict_shl`] (and similar for other integer types)
let impl_9__strict_shl (x: u64) (n: u32)
    : Prims.Pure u64 (requires n <. impl_9__BITS) (fun _ -> Prims.l_True) =
  if n <. impl_9__BITS then x <<! n else Core_models.Panicking.Internal.panic #u64 ()

/// See [`std::primitive::u8::strict_shr`] (and similar for other integer types)
let impl_9__strict_shr (x: u64) (n: u32)
    : Prims.Pure u64 (requires n <. impl_9__BITS) (fun _ -> Prims.l_True) =
  if n <. impl_9__BITS then x >>! n else Core_models.Panicking.Internal.panic #u64 ()

/// See [`std::primitive::u8::unchecked_shl`] (and similar for other integer types)
let impl_9__unchecked_shl (x: u64) (n: u32)
    : Prims.Pure u64 (requires n <. impl_9__BITS) (fun _ -> Prims.l_True) = x <<! n

/// See [`std::primitive::u8::unchecked_shr`] (and similar for other integer types)
let impl_9__unchecked_shr (x: u64) (n: u32)
    : Prims.Pure u64 (requires n <. impl_9__BITS) (fun _ -> Prims.l_True) = x >>! n

/// See [`std::primitive::u8::unchecked_shl_exact`] (and similar for other unsigned integer types)
let impl_9__unchecked_shl_exact (x: u64) (n: u32)
    : Prims.Pure u64
      (requires n <=. (impl_9__leading_zeros x <: u32) && n <. impl_9__BITS)
      (fun _ -> Prims.l_True) = x <<! n

/// See [`std::primitive::u8::unchecked_shr_exact`] (and similar for other integer types)
let impl_9__unchecked_shr_exact (x: u64) (n: u32)
    : Prims.Pure u64
      (requires n <=. (impl_9__trailing_zeros x <: u32) && n <. impl_9__BITS)
      (fun _ -> Prims.l_True) = x >>! n

/// See [`std::primitive::u8::funnel_shl`] (and similar for other unsigned integer types)
let impl_9__funnel_shl (x y: u64) (n: u32)
    : Prims.Pure u64 (requires n <. impl_9__BITS) (fun _ -> Prims.l_True) =
  if n =. mk_u32 0
  then x
  else
    (impl_9__wrapping_shl x n <: u64) |. (impl_9__wrapping_shr y (impl_9__BITS -! n <: u32) <: u64)

/// See [`std::primitive::u8::funnel_shr`] (and similar for other unsigned integer types)
let impl_9__funnel_shr (x y: u64) (n: u32)
    : Prims.Pure u64 (requires n <. impl_9__BITS) (fun _ -> Prims.l_True) =
  if n =. mk_u32 0
  then y
  else
    (impl_9__wrapping_shr y n <: u64) |. (impl_9__wrapping_shl x (impl_9__BITS -! n <: u32) <: u64)

/// See [`std::primitive::u8::unchecked_disjoint_bitor`] (and similar for other unsigned integer types)
let impl_9__unchecked_disjoint_bitor (x y: u64)
    : Prims.Pure u64 (requires (x &. y <: u64) =. mk_u64 0) (fun _ -> Prims.l_True) = x |. y

/// See [`std::primitive::u8::next_power_of_two`] (and similar for other unsigned integer types)
assume
val impl_9__next_power_of_two': x: u64
  -> Prims.Pure u64
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine (mk_i32 2) <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        ((Rust_primitives.Hax.Int.from_machine impl_9__MAX <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine (mk_i32 1) <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True)

unfold
let impl_9__next_power_of_two = impl_9__next_power_of_two'

/// See [`std::primitive::u8::MIN`] (and similar for other unsigned integer types)
let impl_10__MIN: u128 = mk_u128 0

/// See [`std::primitive::u8::MAX`] (and similar for other unsigned integer types)
let impl_10__MAX: u128 = mk_u128 340282366920938463463374607431768211455

/// See [`std::primitive::u8::BITS`] (and similar for other unsigned integer types)
let impl_10__BITS: u32 = mk_u32 128

/// See [`std::primitive::u8::wrapping_add`] (and similar for other unsigned integer types)
let impl_10__wrapping_add (x y: u128) : u128 = Rust_primitives.Arithmetic.wrapping_add_u128 x y

/// See [`std::primitive::u8::saturating_add`] (and similar for other integer types)
let impl_10__saturating_add (x y: u128) : u128 = Rust_primitives.Arithmetic.saturating_add_u128 x y

/// See [`std::primitive::u8::overflowing_add`] (and similar for other integer types)
let impl_10__overflowing_add (x y: u128) : (u128 & bool) =
  Rust_primitives.Arithmetic.overflowing_add_u128 x y

/// See [`std::primitive::u8::wrapping_sub`] (and similar for other integer types)
let impl_10__wrapping_sub (x y: u128) : u128 = Rust_primitives.Arithmetic.wrapping_sub_u128 x y

/// See [`std::primitive::u8::saturating_sub`] (and similar for other integer types)
let impl_10__saturating_sub (x y: u128) : u128 = Rust_primitives.Arithmetic.saturating_sub_u128 x y

/// See [`std::primitive::u8::overflowing_sub`] (and similar for other integer types)
let impl_10__overflowing_sub (x y: u128) : (u128 & bool) =
  Rust_primitives.Arithmetic.overflowing_sub_u128 x y

/// See [`std::primitive::u8::wrapping_mul`] (and similar for other integer types)
let impl_10__wrapping_mul (x y: u128) : u128 = Rust_primitives.Arithmetic.wrapping_mul_u128 x y

/// See [`std::primitive::u8::saturating_mul`] (and similar for other integer types)
let impl_10__saturating_mul (x y: u128) : u128 = Rust_primitives.Arithmetic.saturating_mul_u128 x y

/// See [`std::primitive::u8::overflowing_mul`] (and similar for other integer types)
let impl_10__overflowing_mul (x y: u128) : (u128 & bool) =
  Rust_primitives.Arithmetic.overflowing_mul_u128 x y

/// See [`std::primitive::u8::pow`] (and similar for other integer types)
let impl_10__pow (x: u128) (exp: u32) : u128 = Rust_primitives.Arithmetic.pow_u128 x exp

/// See [`std::primitive::u8::overflowing_pow`] (and similar for other integer types)
let impl_10__overflowing_pow (x: u128) (exp: u32) : (u128 & bool) =
  Rust_primitives.Arithmetic.overflowing_pow_u128 x exp

/// See [`std::primitive::u8::count_ones`] (and similar for other integer types)
let impl_10__count_ones (x: u128) : u32 = Rust_primitives.Arithmetic.count_ones_u128 x

/// See [`std::primitive::u8::rotate_right`] (and similar for other integer types)
assume
val impl_10__rotate_right': x: u128 -> n: u32 -> u128

unfold
let impl_10__rotate_right = impl_10__rotate_right'

/// See [`std::primitive::u8::rotate_left`] (and similar for other integer types)
assume
val impl_10__rotate_left': x: u128 -> n: u32 -> u128

unfold
let impl_10__rotate_left = impl_10__rotate_left'

/// See [`std::primitive::u8::leading_zeros`] (and similar for other integer types)
assume
val impl_10__leading_zeros': x: u128 -> u32

unfold
let impl_10__leading_zeros = impl_10__leading_zeros'

/// See [`std::primitive::u8::ilog2`] (and similar for other integer types)
assume
val impl_10__ilog2': x: u128 -> u32

unfold
let impl_10__ilog2 = impl_10__ilog2'

/// See [`std::primitive::u8::from_be_bytes`] (and similar for other integer types)
assume
val impl_10__from_be_bytes': bytes: t_Array u8 (mk_usize 16) -> u128

unfold
let impl_10__from_be_bytes = impl_10__from_be_bytes'

/// See [`std::primitive::u8::from_le_bytes`] (and similar for other integer types)
assume
val impl_10__from_le_bytes': bytes: t_Array u8 (mk_usize 16) -> u128

unfold
let impl_10__from_le_bytes = impl_10__from_le_bytes'

/// See [`std::primitive::u8::to_be_bytes`] (and similar for other integer types)
assume
val impl_10__to_be_bytes': bytes: u128 -> t_Array u8 (mk_usize 16)

unfold
let impl_10__to_be_bytes = impl_10__to_be_bytes'

/// See [`std::primitive::u8::to_le_bytes`] (and similar for other integer types)
assume
val impl_10__to_le_bytes': bytes: u128 -> t_Array u8 (mk_usize 16)

unfold
let impl_10__to_le_bytes = impl_10__to_le_bytes'

/// See [`std::primitive::u8::is_power_of_two`] (and similar for other unsigned integer types)
let impl_10__is_power_of_two (x: u128) : bool =
  x <>. mk_u128 0 && (x &. (x -! mk_u128 1 <: u128) <: u128) =. mk_u128 0

/// See [`std::primitive::u8::is_multiple_of`] (and similar for other unsigned integer types)
let impl_10__is_multiple_of (x y: u128) : bool =
  if y =. mk_u128 0 then x =. mk_u128 0 else (x %! y <: u128) =. mk_u128 0

/// See [`std::primitive::u8::wrapping_neg`] (and similar for other integer types)
let impl_10__wrapping_neg (x: u128) : u128 =
  Rust_primitives.Arithmetic.wrapping_sub_u128 (mk_u128 0) x

/// See [`std::primitive::u8::min_value`] (and similar for other integer types)
let impl_10__min_value (_: Prims.unit) : u128 = impl_10__MIN

/// See [`std::primitive::u8::max_value`] (and similar for other integer types)
let impl_10__max_value (_: Prims.unit) : u128 = impl_10__MAX

/// See [`std::primitive::u8::cast_signed`] (and similar for other unsigned integer types)
let impl_10__cast_signed (x: u128) : i128 = cast (x <: u128) <: i128

/// See [`std::primitive::u8::count_zeros`] (and similar for other integer types)
let impl_10__count_zeros (x: u128) : u32 = impl_10__BITS -! (impl_10__count_ones x <: u32)

/// See [`std::primitive::u8::overflowing_neg`] (and similar for other integer types)
let impl_10__overflowing_neg (x: u128) : (u128 & bool) =
  impl_10__wrapping_neg x, x <>. mk_u128 0 <: (u128 & bool)

/// See [`std::primitive::u8::wrapping_pow`] (and similar for other integer types)
let impl_10__wrapping_pow (x: u128) (exp: u32) : u128 =
  let (result: u128), (_: bool) = impl_10__overflowing_pow x exp in
  result

/// See [`std::primitive::u8::saturating_pow`] (and similar for other unsigned integer types)
let impl_10__saturating_pow (x: u128) (exp: u32) : u128 =
  let (result: u128), (overflowed: bool) = impl_10__overflowing_pow x exp in
  if overflowed then impl_10__MAX else result

/// See [`std::primitive::u8::abs_diff`] (and similar for other unsigned integer types)
let impl_10__abs_diff (x y: u128) : u128 = if x <. y then y -! x else x -! y

/// See [`std::primitive::u8::midpoint`] (and similar for other unsigned integer types)
let impl_10__midpoint (x y: u128) : u128 =
  impl_10__wrapping_add ((x ^. y <: u128) >>! mk_i32 1 <: u128) (x &. y <: u128)

/// See [`std::primitive::u8::wrapping_add_signed`] (and similar for other unsigned integer types)
let impl_10__wrapping_add_signed (x: u128) (y: i128) : u128 =
  impl_10__wrapping_add x (cast (y <: i128) <: u128)

/// See [`std::primitive::u8::wrapping_sub_signed`] (and similar for other unsigned integer types)
let impl_10__wrapping_sub_signed (x: u128) (y: i128) : u128 =
  impl_10__wrapping_sub x (cast (y <: i128) <: u128)

/// See [`std::primitive::u8::overflowing_add_signed`] (and similar for other unsigned integer types)
let impl_10__overflowing_add_signed (x: u128) (y: i128) : (u128 & bool) =
  let (result: u128), (overflowed: bool) = impl_10__overflowing_add x (cast (y <: i128) <: u128) in
  result, overflowed <>. (y <. mk_i128 0 <: bool) <: (u128 & bool)

/// See [`std::primitive::u8::overflowing_sub_signed`] (and similar for other unsigned integer types)
let impl_10__overflowing_sub_signed (x: u128) (y: i128) : (u128 & bool) =
  let (result: u128), (overflowed: bool) = impl_10__overflowing_sub x (cast (y <: i128) <: u128) in
  result, overflowed <>. (y <. mk_i128 0 <: bool) <: (u128 & bool)

/// See [`std::primitive::u8::saturating_add_signed`] (and similar for other unsigned integer types)
let impl_10__saturating_add_signed (x: u128) (y: i128) : u128 =
  let (result: u128), (overflowed: bool) = impl_10__overflowing_add_signed x y in
  if ~.overflowed then result else if y <. mk_i128 0 then impl_10__MIN else impl_10__MAX

/// See [`std::primitive::u8::saturating_sub_signed`] (and similar for other unsigned integer types)
let impl_10__saturating_sub_signed (x: u128) (y: i128) : u128 =
  let (result: u128), (overflowed: bool) = impl_10__overflowing_sub_signed x y in
  if ~.overflowed then result else if y <. mk_i128 0 then impl_10__MAX else impl_10__MIN

/// See [`std::primitive::u8::trailing_zeros`] (and similar for other integer types)
let impl_10__trailing_zeros (x: u128) : u32 =
  if x =. mk_u128 0
  then impl_10__BITS
  else
    impl_10__count_ones (impl_10__wrapping_sub (x &. (impl_10__wrapping_neg x <: u128) <: u128)
          (mk_u128 1)
        <:
        u128)

/// See [`std::primitive::u8::trailing_ones`] (and similar for other integer types)
let impl_10__trailing_ones (x: u128) : u32 =
  impl_10__trailing_zeros (impl_10__wrapping_sub impl_10__MAX x <: u128)

/// See [`std::primitive::u8::leading_ones`] (and similar for other integer types)
let impl_10__leading_ones (x: u128) : u32 =
  impl_10__leading_zeros (impl_10__wrapping_sub impl_10__MAX x <: u128)

/// See [`std::primitive::u8::bit_width`] (and similar for other unsigned integer types)
assume
val impl_10__bit_width': x: u128 -> u32

unfold
let impl_10__bit_width = impl_10__bit_width'

/// See [`std::primitive::u8::isolate_lowest_one`] (and similar for other integer types)
let impl_10__isolate_lowest_one (x: u128) : u128 = x &. (impl_10__wrapping_neg x <: u128)

/// See [`std::primitive::u8::swap_bytes`] (and similar for other integer types)
let impl_10__swap_bytes (x: u128) : u128 =
  impl_10__from_le_bytes (impl_10__to_be_bytes x <: t_Array u8 (mk_usize 16))

/// See [`std::primitive::u8::to_be`] (and similar for other integer types)
let impl_10__to_be (x: u128) : u128 = impl_10__swap_bytes x

/// See [`std::primitive::u8::to_le`] (and similar for other integer types)
let impl_10__to_le (x: u128) : u128 = x

/// See [`std::primitive::u8::from_be`] (and similar for other integer types)
let impl_10__from_be (x: u128) : u128 = impl_10__swap_bytes x

/// See [`std::primitive::u8::from_le`] (and similar for other integer types)
let impl_10__from_le (x: u128) : u128 = x

/// See [`std::primitive::u8::to_ne_bytes`] (and similar for other integer types)
let impl_10__to_ne_bytes (x: u128) : t_Array u8 (mk_usize 16) = impl_10__to_le_bytes x

/// See [`std::primitive::u8::from_ne_bytes`] (and similar for other integer types)
let impl_10__from_ne_bytes (bytes: t_Array u8 (mk_usize 16)) : u128 = impl_10__from_le_bytes bytes

/// See [`std::primitive::u8::wrapping_shl`] (and similar for other integer types)
let impl_10__wrapping_shl (x: u128) (n: u32) : u128 = x <<! (n %! impl_10__BITS <: u32)

/// See [`std::primitive::u8::wrapping_shr`] (and similar for other integer types)
let impl_10__wrapping_shr (x: u128) (n: u32) : u128 = x >>! (n %! impl_10__BITS <: u32)

/// See [`std::primitive::u8::isolate_highest_one`] (and similar for other integer types)
let impl_10__isolate_highest_one (x: u128) : u128 =
  x &.
  (impl_10__wrapping_shr ((impl_10__MAX /! mk_u128 2 <: u128) +! mk_u128 1 <: u128)
      (impl_10__leading_zeros x <: u32)
    <:
    u128)

/// See [`std::primitive::u8::overflowing_shl`] (and similar for other integer types)
let impl_10__overflowing_shl (x: u128) (n: u32) : (u128 & bool) =
  impl_10__wrapping_shl x n, n >=. impl_10__BITS <: (u128 & bool)

/// See [`std::primitive::u8::overflowing_shr`] (and similar for other integer types)
let impl_10__overflowing_shr (x: u128) (n: u32) : (u128 & bool) =
  impl_10__wrapping_shr x n, n >=. impl_10__BITS <: (u128 & bool)

/// See [`std::primitive::u8::unbounded_shl`] (and similar for other integer types)
let impl_10__unbounded_shl (x: u128) (n: u32) : u128 =
  if n <. impl_10__BITS then x <<! n else mk_u128 0

/// See [`std::primitive::u8::unbounded_shr`] (and similar for other unsigned integer types)
let impl_10__unbounded_shr (x: u128) (n: u32) : u128 =
  if n <. impl_10__BITS then x >>! n else mk_u128 0

/// See [`std::primitive::u8::wrapping_next_power_of_two`] (and similar for other unsigned integer types)
let impl_10__wrapping_next_power_of_two (x: u128) : u128 =
  if x <=. mk_u128 1
  then mk_u128 1
  else
    impl_10__wrapping_add (impl_10__MAX >>!
        ((impl_10__leading_zeros (x -! mk_u128 1 <: u128) <: u32) %! impl_10__BITS <: u32)
        <:
        u128)
      (mk_u128 1)

/// See [`std::primitive::u8::reverse_bits`] (and similar for other unsigned integer types)
let impl_10__reverse_bits (x: u128) : u128 =
  let m1:u128 = impl_10__MAX /! mk_u128 3 in
  let m2:u128 = impl_10__MAX /! mk_u128 5 in
  let m4:u128 = impl_10__MAX /! mk_u128 17 in
  let x:u128 =
    (impl_10__wrapping_shl (x &. m1 <: u128) (mk_u32 1) <: u128) |.
    ((impl_10__wrapping_shr x (mk_u32 1) <: u128) &. m1 <: u128)
  in
  let x:u128 =
    (impl_10__wrapping_shl (x &. m2 <: u128) (mk_u32 2) <: u128) |.
    ((impl_10__wrapping_shr x (mk_u32 2) <: u128) &. m2 <: u128)
  in
  let x:u128 =
    (impl_10__wrapping_shl (x &. m4 <: u128) (mk_u32 4) <: u128) |.
    ((impl_10__wrapping_shr x (mk_u32 4) <: u128) &. m4 <: u128)
  in
  impl_10__swap_bytes x

/// See [`std::primitive::u8::widening_mul`] (and similar for other unsigned integer types)
let impl_10__widening_mul (x y: u128) : (u128 & u128) =
  let half:u32 = impl_10__BITS /! mk_u32 2 in
  let lo_mask:u128 = impl_10__wrapping_shr impl_10__MAX half in
  let xl:u128 = x &. lo_mask in
  let xh:u128 = impl_10__wrapping_shr x half in
  let yl:u128 = y &. lo_mask in
  let yh:u128 = impl_10__wrapping_shr y half in
  let ll:u128 = impl_10__wrapping_mul xl yl in
  let lh:u128 = impl_10__wrapping_mul xl yh in
  let hl:u128 = impl_10__wrapping_mul xh yl in
  let hh:u128 = impl_10__wrapping_mul xh yh in
  let mid:u128 =
    impl_10__wrapping_add (impl_10__wrapping_add (impl_10__wrapping_shr ll half <: u128)
          (lh &. lo_mask <: u128)
        <:
        u128)
      (hl &. lo_mask <: u128)
  in
  let low:u128 =
    (ll &. lo_mask <: u128) |. (impl_10__wrapping_shl (mid &. lo_mask <: u128) half <: u128)
  in
  let high:u128 =
    impl_10__wrapping_add (impl_10__wrapping_add (impl_10__wrapping_add hh
              (impl_10__wrapping_shr lh half <: u128)
            <:
            u128)
          (impl_10__wrapping_shr hl half <: u128)
        <:
        u128)
      (impl_10__wrapping_shr mid half <: u128)
  in
  low, high <: (u128 & u128)

/// See [`std::primitive::u8::carrying_mul_add`] (and similar for other unsigned integer types)
let impl_10__carrying_mul_add (x y carry add: u128) : (u128 & u128) =
  let (low: u128), (high: u128) = impl_10__widening_mul x y in
  let (low: u128), (c1: bool) = impl_10__overflowing_add low carry in
  let (low: u128), (c2: bool) = impl_10__overflowing_add low add in
  let high:u128 = impl_10__wrapping_add high (if c1 then mk_u128 1 else mk_u128 0) in
  let high:u128 = impl_10__wrapping_add high (if c2 then mk_u128 1 else mk_u128 0) in
  low, high <: (u128 & u128)

/// See [`std::primitive::u8::carrying_mul`] (and similar for other unsigned integer types)
let impl_10__carrying_mul (x y carry: u128) : (u128 & u128) =
  impl_10__carrying_mul_add x y carry (mk_u128 0)

/// See [`std::primitive::u8::carrying_add`] (and similar for other integer types)
let impl_10__carrying_add (x y: u128) (carry: bool) : (u128 & bool) =
  let (a: u128), (c1: bool) = impl_10__overflowing_add x y in
  let (b: u128), (c2: bool) = impl_10__overflowing_add a (if carry then mk_u128 1 else mk_u128 0) in
  b, c1 || c2 <: (u128 & bool)

/// See [`std::primitive::u8::borrowing_sub`] (and similar for other integer types)
let impl_10__borrowing_sub (x y: u128) (borrow: bool) : (u128 & bool) =
  let (a: u128), (c1: bool) = impl_10__overflowing_sub x y in
  let (b: u128), (c2: bool) =
    impl_10__overflowing_sub a (if borrow then mk_u128 1 else mk_u128 0)
  in
  b, c1 || c2 <: (u128 & bool)

/// See [`std::primitive::u8::unchecked_add`] (and similar for other integer types)
let impl_10__unchecked_add (x y: u128)
    : Prims.Pure u128
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_10__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) = x +! y

/// See [`std::primitive::u8::unchecked_sub`] (and similar for other integer types)
let impl_10__unchecked_sub (x y: u128) : Prims.Pure u128 (requires x >=. y) (fun _ -> Prims.l_True) =
  x -! y

/// See [`std::primitive::u8::unchecked_mul`] (and similar for other integer types)
let impl_10__unchecked_mul (x y: u128)
    : Prims.Pure u128
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_10__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) = x *! y

/// See [`std::primitive::u8::rem_euclid`] (and similar for other integer types)
let impl_10__rem_euclid (x y: u128)
    : Prims.Pure u128 (requires y <>. mk_u128 0) (fun _ -> Prims.l_True) =
  Rust_primitives.Arithmetic.rem_euclid_u128 x y

/// See [`std::primitive::u8::unchecked_div`] (and similar for other integer types)
let impl_10__unchecked_div (x y: u128)
    : Prims.Pure u128 (requires y <>. mk_u128 0) (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::unchecked_rem`] (and similar for other integer types)
let impl_10__unchecked_rem (x y: u128)
    : Prims.Pure u128 (requires y <>. mk_u128 0) (fun _ -> Prims.l_True) = x %! y

/// See [`std::primitive::u8::div_ceil`] (and similar for other unsigned integer types)
let impl_10__div_ceil (x y: u128)
    : Prims.Pure u128 (requires y <>. mk_u128 0) (fun _ -> Prims.l_True) =
  let d:u128 = x /! y in
  let r:u128 = x %! y in
  if r >. mk_u128 0 then d +! mk_u128 1 else d

/// See [`std::primitive::u8::strict_neg`] (and similar for other integer types)
let impl_10__strict_neg (x: u128)
    : Prims.Pure u128 (requires x =. mk_u128 0) (fun _ -> Prims.l_True) =
  if x =. mk_u128 0 then mk_u128 0 else Core_models.Panicking.Internal.panic #u128 ()

/// See [`std::primitive::u8::strict_pow`] (and similar for other integer types)
let impl_10__strict_pow (x: u128) (exp: u32)
    : Prims.Pure u128
      (requires (impl_10__overflowing_pow x exp <: (u128 & bool))._2 =. false)
      (fun _ -> Prims.l_True) =
  let (result: u128), (overflowed: bool) = impl_10__overflowing_pow x exp in
  if overflowed then Core_models.Panicking.Internal.panic #u128 () else result

/// See [`std::primitive::u8::strict_add`] (and similar for other integer types)
let impl_10__strict_add (x y: u128)
    : Prims.Pure u128
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_10__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: u128), (overflowed: bool) = impl_10__overflowing_add x y in
  if overflowed then Core_models.Panicking.Internal.panic #u128 () else result

/// See [`std::primitive::u8::strict_sub`] (and similar for other integer types)
let impl_10__strict_sub (x y: u128) : Prims.Pure u128 (requires x >=. y) (fun _ -> Prims.l_True) =
  let (result: u128), (overflowed: bool) = impl_10__overflowing_sub x y in
  if overflowed then Core_models.Panicking.Internal.panic #u128 () else result

/// See [`std::primitive::u8::strict_mul`] (and similar for other integer types)
let impl_10__strict_mul (x y: u128)
    : Prims.Pure u128
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_10__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: u128), (overflowed: bool) = impl_10__overflowing_mul x y in
  if overflowed then Core_models.Panicking.Internal.panic #u128 () else result

/// See [`std::primitive::u8::wrapping_div`] (and similar for other unsigned integer types)
let impl_10__wrapping_div (x y: u128)
    : Prims.Pure u128 (requires y <>. mk_u128 0) (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::wrapping_rem`] (and similar for other unsigned integer types)
let impl_10__wrapping_rem (x y: u128)
    : Prims.Pure u128 (requires y <>. mk_u128 0) (fun _ -> Prims.l_True) = x %! y

/// See [`std::primitive::u8::wrapping_div_euclid`] (and similar for other unsigned integer types)
let impl_10__wrapping_div_euclid (x y: u128)
    : Prims.Pure u128 (requires y <>. mk_u128 0) (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::wrapping_rem_euclid`] (and similar for other unsigned integer types)
let impl_10__wrapping_rem_euclid (x y: u128)
    : Prims.Pure u128 (requires y <>. mk_u128 0) (fun _ -> Prims.l_True) = x %! y

/// See [`std::primitive::u8::saturating_div`] (and similar for other unsigned integer types)
let impl_10__saturating_div (x y: u128)
    : Prims.Pure u128 (requires y <>. mk_u128 0) (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::strict_div`] (and similar for other unsigned integer types)
let impl_10__strict_div (x y: u128)
    : Prims.Pure u128 (requires y <>. mk_u128 0) (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::strict_rem`] (and similar for other unsigned integer types)
let impl_10__strict_rem (x y: u128)
    : Prims.Pure u128 (requires y <>. mk_u128 0) (fun _ -> Prims.l_True) = x %! y

/// See [`std::primitive::u8::strict_div_euclid`] (and similar for other unsigned integer types)
let impl_10__strict_div_euclid (x y: u128)
    : Prims.Pure u128 (requires y <>. mk_u128 0) (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::strict_rem_euclid`] (and similar for other unsigned integer types)
let impl_10__strict_rem_euclid (x y: u128)
    : Prims.Pure u128 (requires y <>. mk_u128 0) (fun _ -> Prims.l_True) = x %! y

/// See [`std::primitive::u8::div_euclid`] (and similar for other unsigned integer types)
let impl_10__div_euclid (x y: u128)
    : Prims.Pure u128 (requires y <>. mk_u128 0) (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::div_floor`] (and similar for other unsigned integer types)
let impl_10__div_floor (x y: u128)
    : Prims.Pure u128 (requires y <>. mk_u128 0) (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::overflowing_div`] (and similar for other unsigned integer types)
let impl_10__overflowing_div (x y: u128)
    : Prims.Pure (u128 & bool) (requires y <>. mk_u128 0) (fun _ -> Prims.l_True) =
  x /! y, false <: (u128 & bool)

/// See [`std::primitive::u8::overflowing_rem`] (and similar for other unsigned integer types)
let impl_10__overflowing_rem (x y: u128)
    : Prims.Pure (u128 & bool) (requires y <>. mk_u128 0) (fun _ -> Prims.l_True) =
  x %! y, false <: (u128 & bool)

/// See [`std::primitive::u8::overflowing_div_euclid`] (and similar for other unsigned integer types)
let impl_10__overflowing_div_euclid (x y: u128)
    : Prims.Pure (u128 & bool) (requires y <>. mk_u128 0) (fun _ -> Prims.l_True) =
  x /! y, false <: (u128 & bool)

/// See [`std::primitive::u8::overflowing_rem_euclid`] (and similar for other unsigned integer types)
let impl_10__overflowing_rem_euclid (x y: u128)
    : Prims.Pure (u128 & bool) (requires y <>. mk_u128 0) (fun _ -> Prims.l_True) =
  x %! y, false <: (u128 & bool)

/// See [`std::primitive::u8::unchecked_div_exact`] (and similar for other unsigned integer types)
let impl_10__unchecked_div_exact (x y: u128)
    : Prims.Pure u128
      (requires y <>. mk_u128 0 && (x %! y <: u128) =. mk_u128 0)
      (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::next_multiple_of`] (and similar for other unsigned integer types)
let impl_10__next_multiple_of (x y: u128)
    : Prims.Pure u128
      (requires
        y <>. mk_u128 0 &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine ((y -! (x %! y <: u128) <: u128) %! y <: u128)
            <:
            Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_10__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) = x +! ((y -! (x %! y <: u128) <: u128) %! y <: u128)

/// See [`std::primitive::u8::strict_add_signed`] (and similar for other unsigned integer types)
let impl_10__strict_add_signed (x: u128) (y: i128)
    : Prims.Pure u128
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_10__MIN <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_10__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: u128), (overflowed: bool) = impl_10__overflowing_add_signed x y in
  if overflowed then Core_models.Panicking.Internal.panic #u128 () else result

/// See [`std::primitive::u8::strict_sub_signed`] (and similar for other unsigned integer types)
let impl_10__strict_sub_signed (x: u128) (y: i128)
    : Prims.Pure u128
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_10__MIN <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_10__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: u128), (overflowed: bool) = impl_10__overflowing_sub_signed x y in
  if overflowed then Core_models.Panicking.Internal.panic #u128 () else result

/// See [`std::primitive::u8::strict_shl`] (and similar for other integer types)
let impl_10__strict_shl (x: u128) (n: u32)
    : Prims.Pure u128 (requires n <. impl_10__BITS) (fun _ -> Prims.l_True) =
  if n <. impl_10__BITS then x <<! n else Core_models.Panicking.Internal.panic #u128 ()

/// See [`std::primitive::u8::strict_shr`] (and similar for other integer types)
let impl_10__strict_shr (x: u128) (n: u32)
    : Prims.Pure u128 (requires n <. impl_10__BITS) (fun _ -> Prims.l_True) =
  if n <. impl_10__BITS then x >>! n else Core_models.Panicking.Internal.panic #u128 ()

/// See [`std::primitive::u8::unchecked_shl`] (and similar for other integer types)
let impl_10__unchecked_shl (x: u128) (n: u32)
    : Prims.Pure u128 (requires n <. impl_10__BITS) (fun _ -> Prims.l_True) = x <<! n

/// See [`std::primitive::u8::unchecked_shr`] (and similar for other integer types)
let impl_10__unchecked_shr (x: u128) (n: u32)
    : Prims.Pure u128 (requires n <. impl_10__BITS) (fun _ -> Prims.l_True) = x >>! n

/// See [`std::primitive::u8::unchecked_shl_exact`] (and similar for other unsigned integer types)
let impl_10__unchecked_shl_exact (x: u128) (n: u32)
    : Prims.Pure u128
      (requires n <=. (impl_10__leading_zeros x <: u32) && n <. impl_10__BITS)
      (fun _ -> Prims.l_True) = x <<! n

/// See [`std::primitive::u8::unchecked_shr_exact`] (and similar for other integer types)
let impl_10__unchecked_shr_exact (x: u128) (n: u32)
    : Prims.Pure u128
      (requires n <=. (impl_10__trailing_zeros x <: u32) && n <. impl_10__BITS)
      (fun _ -> Prims.l_True) = x >>! n

/// See [`std::primitive::u8::funnel_shl`] (and similar for other unsigned integer types)
let impl_10__funnel_shl (x y: u128) (n: u32)
    : Prims.Pure u128 (requires n <. impl_10__BITS) (fun _ -> Prims.l_True) =
  if n =. mk_u32 0
  then x
  else
    (impl_10__wrapping_shl x n <: u128) |.
    (impl_10__wrapping_shr y (impl_10__BITS -! n <: u32) <: u128)

/// See [`std::primitive::u8::funnel_shr`] (and similar for other unsigned integer types)
let impl_10__funnel_shr (x y: u128) (n: u32)
    : Prims.Pure u128 (requires n <. impl_10__BITS) (fun _ -> Prims.l_True) =
  if n =. mk_u32 0
  then y
  else
    (impl_10__wrapping_shr y n <: u128) |.
    (impl_10__wrapping_shl x (impl_10__BITS -! n <: u32) <: u128)

/// See [`std::primitive::u8::unchecked_disjoint_bitor`] (and similar for other unsigned integer types)
let impl_10__unchecked_disjoint_bitor (x y: u128)
    : Prims.Pure u128 (requires (x &. y <: u128) =. mk_u128 0) (fun _ -> Prims.l_True) = x |. y

/// See [`std::primitive::u8::next_power_of_two`] (and similar for other unsigned integer types)
assume
val impl_10__next_power_of_two': x: u128
  -> Prims.Pure u128
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine (mk_i32 2) <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        ((Rust_primitives.Hax.Int.from_machine impl_10__MAX <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine (mk_i32 1) <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True)

unfold
let impl_10__next_power_of_two = impl_10__next_power_of_two'

/// See [`std::primitive::u8::MIN`] (and similar for other unsigned integer types)
let impl_11__MIN: usize = mk_usize 0

/// See [`std::primitive::u8::MAX`] (and similar for other unsigned integer types)
let impl_11__MAX: usize = Rust_primitives.Arithmetic.v_USIZE_MAX

/// See [`std::primitive::u8::BITS`] (and similar for other unsigned integer types)
let impl_11__BITS: u32 = Rust_primitives.Arithmetic.v_SIZE_BITS

/// See [`std::primitive::u8::wrapping_add`] (and similar for other unsigned integer types)
let impl_11__wrapping_add (x y: usize) : usize = Rust_primitives.Arithmetic.wrapping_add_usize x y

/// See [`std::primitive::u8::saturating_add`] (and similar for other integer types)
let impl_11__saturating_add (x y: usize) : usize =
  Rust_primitives.Arithmetic.saturating_add_usize x y

/// See [`std::primitive::u8::overflowing_add`] (and similar for other integer types)
let impl_11__overflowing_add (x y: usize) : (usize & bool) =
  Rust_primitives.Arithmetic.overflowing_add_usize x y

/// See [`std::primitive::u8::wrapping_sub`] (and similar for other integer types)
let impl_11__wrapping_sub (x y: usize) : usize = Rust_primitives.Arithmetic.wrapping_sub_usize x y

/// See [`std::primitive::u8::saturating_sub`] (and similar for other integer types)
let impl_11__saturating_sub (x y: usize) : usize =
  Rust_primitives.Arithmetic.saturating_sub_usize x y

/// See [`std::primitive::u8::overflowing_sub`] (and similar for other integer types)
let impl_11__overflowing_sub (x y: usize) : (usize & bool) =
  Rust_primitives.Arithmetic.overflowing_sub_usize x y

/// See [`std::primitive::u8::wrapping_mul`] (and similar for other integer types)
let impl_11__wrapping_mul (x y: usize) : usize = Rust_primitives.Arithmetic.wrapping_mul_usize x y

/// See [`std::primitive::u8::saturating_mul`] (and similar for other integer types)
let impl_11__saturating_mul (x y: usize) : usize =
  Rust_primitives.Arithmetic.saturating_mul_usize x y

/// See [`std::primitive::u8::overflowing_mul`] (and similar for other integer types)
let impl_11__overflowing_mul (x y: usize) : (usize & bool) =
  Rust_primitives.Arithmetic.overflowing_mul_usize x y

/// See [`std::primitive::u8::pow`] (and similar for other integer types)
let impl_11__pow (x: usize) (exp: u32) : usize = Rust_primitives.Arithmetic.pow_usize x exp

/// See [`std::primitive::u8::overflowing_pow`] (and similar for other integer types)
let impl_11__overflowing_pow (x: usize) (exp: u32) : (usize & bool) =
  Rust_primitives.Arithmetic.overflowing_pow_usize x exp

/// See [`std::primitive::u8::count_ones`] (and similar for other integer types)
let impl_11__count_ones (x: usize) : u32 = Rust_primitives.Arithmetic.count_ones_usize x

/// See [`std::primitive::u8::rotate_right`] (and similar for other integer types)
assume
val impl_11__rotate_right': x: usize -> n: u32 -> usize

unfold
let impl_11__rotate_right = impl_11__rotate_right'

/// See [`std::primitive::u8::rotate_left`] (and similar for other integer types)
assume
val impl_11__rotate_left': x: usize -> n: u32 -> usize

unfold
let impl_11__rotate_left = impl_11__rotate_left'

/// See [`std::primitive::u8::leading_zeros`] (and similar for other integer types)
assume
val impl_11__leading_zeros': x: usize -> u32

unfold
let impl_11__leading_zeros = impl_11__leading_zeros'

/// See [`std::primitive::u8::ilog2`] (and similar for other integer types)
assume
val impl_11__ilog2': x: usize -> u32

unfold
let impl_11__ilog2 = impl_11__ilog2'

/// See [`std::primitive::u8::from_be_bytes`] (and similar for other integer types)
assume
val impl_11__from_be_bytes': bytes: t_Array u8 (mk_usize 8) -> usize

unfold
let impl_11__from_be_bytes = impl_11__from_be_bytes'

/// See [`std::primitive::u8::from_le_bytes`] (and similar for other integer types)
assume
val impl_11__from_le_bytes': bytes: t_Array u8 (mk_usize 8) -> usize

unfold
let impl_11__from_le_bytes = impl_11__from_le_bytes'

/// See [`std::primitive::u8::to_be_bytes`] (and similar for other integer types)
assume
val impl_11__to_be_bytes': bytes: usize -> t_Array u8 (mk_usize 8)

unfold
let impl_11__to_be_bytes = impl_11__to_be_bytes'

/// See [`std::primitive::u8::to_le_bytes`] (and similar for other integer types)
assume
val impl_11__to_le_bytes': bytes: usize -> t_Array u8 (mk_usize 8)

unfold
let impl_11__to_le_bytes = impl_11__to_le_bytes'

/// See [`std::primitive::u8::is_power_of_two`] (and similar for other unsigned integer types)
let impl_11__is_power_of_two (x: usize) : bool =
  x <>. mk_usize 0 && (x &. (x -! mk_usize 1 <: usize) <: usize) =. mk_usize 0

/// See [`std::primitive::u8::is_multiple_of`] (and similar for other unsigned integer types)
let impl_11__is_multiple_of (x y: usize) : bool =
  if y =. mk_usize 0 then x =. mk_usize 0 else (x %! y <: usize) =. mk_usize 0

/// See [`std::primitive::u8::wrapping_neg`] (and similar for other integer types)
let impl_11__wrapping_neg (x: usize) : usize =
  Rust_primitives.Arithmetic.wrapping_sub_usize (mk_usize 0) x

/// See [`std::primitive::u8::min_value`] (and similar for other integer types)
let impl_11__min_value (_: Prims.unit) : usize = impl_11__MIN

/// See [`std::primitive::u8::max_value`] (and similar for other integer types)
let impl_11__max_value (_: Prims.unit) : usize = impl_11__MAX

/// See [`std::primitive::u8::cast_signed`] (and similar for other unsigned integer types)
let impl_11__cast_signed (x: usize) : isize = cast (x <: usize) <: isize

/// See [`std::primitive::u8::count_zeros`] (and similar for other integer types)
let impl_11__count_zeros (x: usize) : u32 = impl_11__BITS -! (impl_11__count_ones x <: u32)

/// See [`std::primitive::u8::overflowing_neg`] (and similar for other integer types)
let impl_11__overflowing_neg (x: usize) : (usize & bool) =
  impl_11__wrapping_neg x, x <>. mk_usize 0 <: (usize & bool)

/// See [`std::primitive::u8::wrapping_pow`] (and similar for other integer types)
let impl_11__wrapping_pow (x: usize) (exp: u32) : usize =
  let (result: usize), (_: bool) = impl_11__overflowing_pow x exp in
  result

/// See [`std::primitive::u8::saturating_pow`] (and similar for other unsigned integer types)
let impl_11__saturating_pow (x: usize) (exp: u32) : usize =
  let (result: usize), (overflowed: bool) = impl_11__overflowing_pow x exp in
  if overflowed then impl_11__MAX else result

/// See [`std::primitive::u8::abs_diff`] (and similar for other unsigned integer types)
let impl_11__abs_diff (x y: usize) : usize = if x <. y then y -! x else x -! y

/// See [`std::primitive::u8::midpoint`] (and similar for other unsigned integer types)
let impl_11__midpoint (x y: usize) : usize =
  impl_11__wrapping_add ((x ^. y <: usize) >>! mk_i32 1 <: usize) (x &. y <: usize)

/// See [`std::primitive::u8::wrapping_add_signed`] (and similar for other unsigned integer types)
let impl_11__wrapping_add_signed (x: usize) (y: isize) : usize =
  impl_11__wrapping_add x (cast (y <: isize) <: usize)

/// See [`std::primitive::u8::wrapping_sub_signed`] (and similar for other unsigned integer types)
let impl_11__wrapping_sub_signed (x: usize) (y: isize) : usize =
  impl_11__wrapping_sub x (cast (y <: isize) <: usize)

/// See [`std::primitive::u8::overflowing_add_signed`] (and similar for other unsigned integer types)
let impl_11__overflowing_add_signed (x: usize) (y: isize) : (usize & bool) =
  let (result: usize), (overflowed: bool) =
    impl_11__overflowing_add x (cast (y <: isize) <: usize)
  in
  result, overflowed <>. (y <. mk_isize 0 <: bool) <: (usize & bool)

/// See [`std::primitive::u8::overflowing_sub_signed`] (and similar for other unsigned integer types)
let impl_11__overflowing_sub_signed (x: usize) (y: isize) : (usize & bool) =
  let (result: usize), (overflowed: bool) =
    impl_11__overflowing_sub x (cast (y <: isize) <: usize)
  in
  result, overflowed <>. (y <. mk_isize 0 <: bool) <: (usize & bool)

/// See [`std::primitive::u8::saturating_add_signed`] (and similar for other unsigned integer types)
let impl_11__saturating_add_signed (x: usize) (y: isize) : usize =
  let (result: usize), (overflowed: bool) = impl_11__overflowing_add_signed x y in
  if ~.overflowed then result else if y <. mk_isize 0 then impl_11__MIN else impl_11__MAX

/// See [`std::primitive::u8::saturating_sub_signed`] (and similar for other unsigned integer types)
let impl_11__saturating_sub_signed (x: usize) (y: isize) : usize =
  let (result: usize), (overflowed: bool) = impl_11__overflowing_sub_signed x y in
  if ~.overflowed then result else if y <. mk_isize 0 then impl_11__MAX else impl_11__MIN

/// See [`std::primitive::u8::trailing_zeros`] (and similar for other integer types)
let impl_11__trailing_zeros (x: usize) : u32 =
  if x =. mk_usize 0
  then impl_11__BITS
  else
    impl_11__count_ones (impl_11__wrapping_sub (x &. (impl_11__wrapping_neg x <: usize) <: usize)
          (mk_usize 1)
        <:
        usize)

/// See [`std::primitive::u8::trailing_ones`] (and similar for other integer types)
let impl_11__trailing_ones (x: usize) : u32 =
  impl_11__trailing_zeros (impl_11__wrapping_sub impl_11__MAX x <: usize)

/// See [`std::primitive::u8::leading_ones`] (and similar for other integer types)
let impl_11__leading_ones (x: usize) : u32 =
  impl_11__leading_zeros (impl_11__wrapping_sub impl_11__MAX x <: usize)

/// See [`std::primitive::u8::bit_width`] (and similar for other unsigned integer types)
assume
val impl_11__bit_width': x: usize -> u32

unfold
let impl_11__bit_width = impl_11__bit_width'

/// See [`std::primitive::u8::isolate_lowest_one`] (and similar for other integer types)
let impl_11__isolate_lowest_one (x: usize) : usize = x &. (impl_11__wrapping_neg x <: usize)

/// See [`std::primitive::u8::swap_bytes`] (and similar for other integer types)
let impl_11__swap_bytes (x: usize) : usize =
  impl_11__from_le_bytes (impl_11__to_be_bytes x <: t_Array u8 (mk_usize 8))

/// See [`std::primitive::u8::to_be`] (and similar for other integer types)
let impl_11__to_be (x: usize) : usize = impl_11__swap_bytes x

/// See [`std::primitive::u8::to_le`] (and similar for other integer types)
let impl_11__to_le (x: usize) : usize = x

/// See [`std::primitive::u8::from_be`] (and similar for other integer types)
let impl_11__from_be (x: usize) : usize = impl_11__swap_bytes x

/// See [`std::primitive::u8::from_le`] (and similar for other integer types)
let impl_11__from_le (x: usize) : usize = x

/// See [`std::primitive::u8::to_ne_bytes`] (and similar for other integer types)
let impl_11__to_ne_bytes (x: usize) : t_Array u8 (mk_usize 8) = impl_11__to_le_bytes x

/// See [`std::primitive::u8::from_ne_bytes`] (and similar for other integer types)
let impl_11__from_ne_bytes (bytes: t_Array u8 (mk_usize 8)) : usize = impl_11__from_le_bytes bytes

/// See [`std::primitive::u8::wrapping_shl`] (and similar for other integer types)
let impl_11__wrapping_shl (x: usize) (n: u32) : usize = x <<! (n %! impl_11__BITS <: u32)

/// See [`std::primitive::u8::wrapping_shr`] (and similar for other integer types)
let impl_11__wrapping_shr (x: usize) (n: u32) : usize = x >>! (n %! impl_11__BITS <: u32)

/// See [`std::primitive::u8::isolate_highest_one`] (and similar for other integer types)
let impl_11__isolate_highest_one (x: usize) : usize =
  x &.
  (impl_11__wrapping_shr ((impl_11__MAX /! mk_usize 2 <: usize) +! mk_usize 1 <: usize)
      (impl_11__leading_zeros x <: u32)
    <:
    usize)

/// See [`std::primitive::u8::overflowing_shl`] (and similar for other integer types)
let impl_11__overflowing_shl (x: usize) (n: u32) : (usize & bool) =
  impl_11__wrapping_shl x n, n >=. impl_11__BITS <: (usize & bool)

/// See [`std::primitive::u8::overflowing_shr`] (and similar for other integer types)
let impl_11__overflowing_shr (x: usize) (n: u32) : (usize & bool) =
  impl_11__wrapping_shr x n, n >=. impl_11__BITS <: (usize & bool)

/// See [`std::primitive::u8::unbounded_shl`] (and similar for other integer types)
let impl_11__unbounded_shl (x: usize) (n: u32) : usize =
  if n <. impl_11__BITS then x <<! n else mk_usize 0

/// See [`std::primitive::u8::unbounded_shr`] (and similar for other unsigned integer types)
let impl_11__unbounded_shr (x: usize) (n: u32) : usize =
  if n <. impl_11__BITS then x >>! n else mk_usize 0

/// See [`std::primitive::u8::wrapping_next_power_of_two`] (and similar for other unsigned integer types)
let impl_11__wrapping_next_power_of_two (x: usize) : usize =
  if x <=. mk_usize 1
  then mk_usize 1
  else
    impl_11__wrapping_add (impl_11__MAX >>!
        ((impl_11__leading_zeros (x -! mk_usize 1 <: usize) <: u32) %! impl_11__BITS <: u32)
        <:
        usize)
      (mk_usize 1)

/// See [`std::primitive::u8::reverse_bits`] (and similar for other unsigned integer types)
let impl_11__reverse_bits (x: usize) : usize =
  let m1:usize = impl_11__MAX /! mk_usize 3 in
  let m2:usize = impl_11__MAX /! mk_usize 5 in
  let m4:usize = impl_11__MAX /! mk_usize 17 in
  let x:usize =
    (impl_11__wrapping_shl (x &. m1 <: usize) (mk_u32 1) <: usize) |.
    ((impl_11__wrapping_shr x (mk_u32 1) <: usize) &. m1 <: usize)
  in
  let x:usize =
    (impl_11__wrapping_shl (x &. m2 <: usize) (mk_u32 2) <: usize) |.
    ((impl_11__wrapping_shr x (mk_u32 2) <: usize) &. m2 <: usize)
  in
  let x:usize =
    (impl_11__wrapping_shl (x &. m4 <: usize) (mk_u32 4) <: usize) |.
    ((impl_11__wrapping_shr x (mk_u32 4) <: usize) &. m4 <: usize)
  in
  impl_11__swap_bytes x

/// See [`std::primitive::u8::widening_mul`] (and similar for other unsigned integer types)
let impl_11__widening_mul (x y: usize) : (usize & usize) =
  let half:u32 = impl_11__BITS /! mk_u32 2 in
  let lo_mask:usize = impl_11__wrapping_shr impl_11__MAX half in
  let xl:usize = x &. lo_mask in
  let xh:usize = impl_11__wrapping_shr x half in
  let yl:usize = y &. lo_mask in
  let yh:usize = impl_11__wrapping_shr y half in
  let ll:usize = impl_11__wrapping_mul xl yl in
  let lh:usize = impl_11__wrapping_mul xl yh in
  let hl:usize = impl_11__wrapping_mul xh yl in
  let hh:usize = impl_11__wrapping_mul xh yh in
  let mid:usize =
    impl_11__wrapping_add (impl_11__wrapping_add (impl_11__wrapping_shr ll half <: usize)
          (lh &. lo_mask <: usize)
        <:
        usize)
      (hl &. lo_mask <: usize)
  in
  let low:usize =
    (ll &. lo_mask <: usize) |. (impl_11__wrapping_shl (mid &. lo_mask <: usize) half <: usize)
  in
  let high:usize =
    impl_11__wrapping_add (impl_11__wrapping_add (impl_11__wrapping_add hh
              (impl_11__wrapping_shr lh half <: usize)
            <:
            usize)
          (impl_11__wrapping_shr hl half <: usize)
        <:
        usize)
      (impl_11__wrapping_shr mid half <: usize)
  in
  low, high <: (usize & usize)

/// See [`std::primitive::u8::carrying_mul_add`] (and similar for other unsigned integer types)
let impl_11__carrying_mul_add (x y carry add: usize) : (usize & usize) =
  let (low: usize), (high: usize) = impl_11__widening_mul x y in
  let (low: usize), (c1: bool) = impl_11__overflowing_add low carry in
  let (low: usize), (c2: bool) = impl_11__overflowing_add low add in
  let high:usize = impl_11__wrapping_add high (if c1 then mk_usize 1 else mk_usize 0) in
  let high:usize = impl_11__wrapping_add high (if c2 then mk_usize 1 else mk_usize 0) in
  low, high <: (usize & usize)

/// See [`std::primitive::u8::carrying_mul`] (and similar for other unsigned integer types)
let impl_11__carrying_mul (x y carry: usize) : (usize & usize) =
  impl_11__carrying_mul_add x y carry (mk_usize 0)

/// See [`std::primitive::u8::carrying_add`] (and similar for other integer types)
let impl_11__carrying_add (x y: usize) (carry: bool) : (usize & bool) =
  let (a: usize), (c1: bool) = impl_11__overflowing_add x y in
  let (b: usize), (c2: bool) =
    impl_11__overflowing_add a (if carry then mk_usize 1 else mk_usize 0)
  in
  b, c1 || c2 <: (usize & bool)

/// See [`std::primitive::u8::borrowing_sub`] (and similar for other integer types)
let impl_11__borrowing_sub (x y: usize) (borrow: bool) : (usize & bool) =
  let (a: usize), (c1: bool) = impl_11__overflowing_sub x y in
  let (b: usize), (c2: bool) =
    impl_11__overflowing_sub a (if borrow then mk_usize 1 else mk_usize 0)
  in
  b, c1 || c2 <: (usize & bool)

/// See [`std::primitive::u8::unchecked_add`] (and similar for other integer types)
let impl_11__unchecked_add (x y: usize)
    : Prims.Pure usize
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_11__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) = x +! y

/// See [`std::primitive::u8::unchecked_sub`] (and similar for other integer types)
let impl_11__unchecked_sub (x y: usize)
    : Prims.Pure usize (requires x >=. y) (fun _ -> Prims.l_True) = x -! y

/// See [`std::primitive::u8::unchecked_mul`] (and similar for other integer types)
let impl_11__unchecked_mul (x y: usize)
    : Prims.Pure usize
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_11__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) = x *! y

/// See [`std::primitive::u8::rem_euclid`] (and similar for other integer types)
let impl_11__rem_euclid (x y: usize)
    : Prims.Pure usize (requires y <>. mk_usize 0) (fun _ -> Prims.l_True) =
  Rust_primitives.Arithmetic.rem_euclid_usize x y

/// See [`std::primitive::u8::unchecked_div`] (and similar for other integer types)
let impl_11__unchecked_div (x y: usize)
    : Prims.Pure usize (requires y <>. mk_usize 0) (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::unchecked_rem`] (and similar for other integer types)
let impl_11__unchecked_rem (x y: usize)
    : Prims.Pure usize (requires y <>. mk_usize 0) (fun _ -> Prims.l_True) = x %! y

/// See [`std::primitive::u8::div_ceil`] (and similar for other unsigned integer types)
let impl_11__div_ceil (x y: usize)
    : Prims.Pure usize (requires y <>. mk_usize 0) (fun _ -> Prims.l_True) =
  let d:usize = x /! y in
  let r:usize = x %! y in
  if r >. mk_usize 0 then d +! mk_usize 1 else d

/// See [`std::primitive::u8::strict_neg`] (and similar for other integer types)
let impl_11__strict_neg (x: usize)
    : Prims.Pure usize (requires x =. mk_usize 0) (fun _ -> Prims.l_True) =
  if x =. mk_usize 0 then mk_usize 0 else Core_models.Panicking.Internal.panic #usize ()

/// See [`std::primitive::u8::strict_pow`] (and similar for other integer types)
let impl_11__strict_pow (x: usize) (exp: u32)
    : Prims.Pure usize
      (requires (impl_11__overflowing_pow x exp <: (usize & bool))._2 =. false)
      (fun _ -> Prims.l_True) =
  let (result: usize), (overflowed: bool) = impl_11__overflowing_pow x exp in
  if overflowed then Core_models.Panicking.Internal.panic #usize () else result

/// See [`std::primitive::u8::strict_add`] (and similar for other integer types)
let impl_11__strict_add (x y: usize)
    : Prims.Pure usize
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_11__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: usize), (overflowed: bool) = impl_11__overflowing_add x y in
  if overflowed then Core_models.Panicking.Internal.panic #usize () else result

/// See [`std::primitive::u8::strict_sub`] (and similar for other integer types)
let impl_11__strict_sub (x y: usize) : Prims.Pure usize (requires x >=. y) (fun _ -> Prims.l_True) =
  let (result: usize), (overflowed: bool) = impl_11__overflowing_sub x y in
  if overflowed then Core_models.Panicking.Internal.panic #usize () else result

/// See [`std::primitive::u8::strict_mul`] (and similar for other integer types)
let impl_11__strict_mul (x y: usize)
    : Prims.Pure usize
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_11__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: usize), (overflowed: bool) = impl_11__overflowing_mul x y in
  if overflowed then Core_models.Panicking.Internal.panic #usize () else result

/// See [`std::primitive::u8::wrapping_div`] (and similar for other unsigned integer types)
let impl_11__wrapping_div (x y: usize)
    : Prims.Pure usize (requires y <>. mk_usize 0) (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::wrapping_rem`] (and similar for other unsigned integer types)
let impl_11__wrapping_rem (x y: usize)
    : Prims.Pure usize (requires y <>. mk_usize 0) (fun _ -> Prims.l_True) = x %! y

/// See [`std::primitive::u8::wrapping_div_euclid`] (and similar for other unsigned integer types)
let impl_11__wrapping_div_euclid (x y: usize)
    : Prims.Pure usize (requires y <>. mk_usize 0) (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::wrapping_rem_euclid`] (and similar for other unsigned integer types)
let impl_11__wrapping_rem_euclid (x y: usize)
    : Prims.Pure usize (requires y <>. mk_usize 0) (fun _ -> Prims.l_True) = x %! y

/// See [`std::primitive::u8::saturating_div`] (and similar for other unsigned integer types)
let impl_11__saturating_div (x y: usize)
    : Prims.Pure usize (requires y <>. mk_usize 0) (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::strict_div`] (and similar for other unsigned integer types)
let impl_11__strict_div (x y: usize)
    : Prims.Pure usize (requires y <>. mk_usize 0) (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::strict_rem`] (and similar for other unsigned integer types)
let impl_11__strict_rem (x y: usize)
    : Prims.Pure usize (requires y <>. mk_usize 0) (fun _ -> Prims.l_True) = x %! y

/// See [`std::primitive::u8::strict_div_euclid`] (and similar for other unsigned integer types)
let impl_11__strict_div_euclid (x y: usize)
    : Prims.Pure usize (requires y <>. mk_usize 0) (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::strict_rem_euclid`] (and similar for other unsigned integer types)
let impl_11__strict_rem_euclid (x y: usize)
    : Prims.Pure usize (requires y <>. mk_usize 0) (fun _ -> Prims.l_True) = x %! y

/// See [`std::primitive::u8::div_euclid`] (and similar for other unsigned integer types)
let impl_11__div_euclid (x y: usize)
    : Prims.Pure usize (requires y <>. mk_usize 0) (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::div_floor`] (and similar for other unsigned integer types)
let impl_11__div_floor (x y: usize)
    : Prims.Pure usize (requires y <>. mk_usize 0) (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::overflowing_div`] (and similar for other unsigned integer types)
let impl_11__overflowing_div (x y: usize)
    : Prims.Pure (usize & bool) (requires y <>. mk_usize 0) (fun _ -> Prims.l_True) =
  x /! y, false <: (usize & bool)

/// See [`std::primitive::u8::overflowing_rem`] (and similar for other unsigned integer types)
let impl_11__overflowing_rem (x y: usize)
    : Prims.Pure (usize & bool) (requires y <>. mk_usize 0) (fun _ -> Prims.l_True) =
  x %! y, false <: (usize & bool)

/// See [`std::primitive::u8::overflowing_div_euclid`] (and similar for other unsigned integer types)
let impl_11__overflowing_div_euclid (x y: usize)
    : Prims.Pure (usize & bool) (requires y <>. mk_usize 0) (fun _ -> Prims.l_True) =
  x /! y, false <: (usize & bool)

/// See [`std::primitive::u8::overflowing_rem_euclid`] (and similar for other unsigned integer types)
let impl_11__overflowing_rem_euclid (x y: usize)
    : Prims.Pure (usize & bool) (requires y <>. mk_usize 0) (fun _ -> Prims.l_True) =
  x %! y, false <: (usize & bool)

/// See [`std::primitive::u8::unchecked_div_exact`] (and similar for other unsigned integer types)
let impl_11__unchecked_div_exact (x y: usize)
    : Prims.Pure usize
      (requires y <>. mk_usize 0 && (x %! y <: usize) =. mk_usize 0)
      (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::next_multiple_of`] (and similar for other unsigned integer types)
let impl_11__next_multiple_of (x y: usize)
    : Prims.Pure usize
      (requires
        y <>. mk_usize 0 &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine ((y -! (x %! y <: usize) <: usize) %! y <: usize)
            <:
            Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_11__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) = x +! ((y -! (x %! y <: usize) <: usize) %! y <: usize)

/// See [`std::primitive::u8::strict_add_signed`] (and similar for other unsigned integer types)
let impl_11__strict_add_signed (x: usize) (y: isize)
    : Prims.Pure usize
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_11__MIN <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_11__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: usize), (overflowed: bool) = impl_11__overflowing_add_signed x y in
  if overflowed then Core_models.Panicking.Internal.panic #usize () else result

/// See [`std::primitive::u8::strict_sub_signed`] (and similar for other unsigned integer types)
let impl_11__strict_sub_signed (x: usize) (y: isize)
    : Prims.Pure usize
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_11__MIN <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_11__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: usize), (overflowed: bool) = impl_11__overflowing_sub_signed x y in
  if overflowed then Core_models.Panicking.Internal.panic #usize () else result

/// See [`std::primitive::u8::strict_shl`] (and similar for other integer types)
let impl_11__strict_shl (x: usize) (n: u32)
    : Prims.Pure usize (requires n <. impl_11__BITS) (fun _ -> Prims.l_True) =
  if n <. impl_11__BITS then x <<! n else Core_models.Panicking.Internal.panic #usize ()

/// See [`std::primitive::u8::strict_shr`] (and similar for other integer types)
let impl_11__strict_shr (x: usize) (n: u32)
    : Prims.Pure usize (requires n <. impl_11__BITS) (fun _ -> Prims.l_True) =
  if n <. impl_11__BITS then x >>! n else Core_models.Panicking.Internal.panic #usize ()

/// See [`std::primitive::u8::unchecked_shl`] (and similar for other integer types)
let impl_11__unchecked_shl (x: usize) (n: u32)
    : Prims.Pure usize (requires n <. impl_11__BITS) (fun _ -> Prims.l_True) = x <<! n

/// See [`std::primitive::u8::unchecked_shr`] (and similar for other integer types)
let impl_11__unchecked_shr (x: usize) (n: u32)
    : Prims.Pure usize (requires n <. impl_11__BITS) (fun _ -> Prims.l_True) = x >>! n

/// See [`std::primitive::u8::unchecked_shl_exact`] (and similar for other unsigned integer types)
let impl_11__unchecked_shl_exact (x: usize) (n: u32)
    : Prims.Pure usize
      (requires n <=. (impl_11__leading_zeros x <: u32) && n <. impl_11__BITS)
      (fun _ -> Prims.l_True) = x <<! n

/// See [`std::primitive::u8::unchecked_shr_exact`] (and similar for other integer types)
let impl_11__unchecked_shr_exact (x: usize) (n: u32)
    : Prims.Pure usize
      (requires n <=. (impl_11__trailing_zeros x <: u32) && n <. impl_11__BITS)
      (fun _ -> Prims.l_True) = x >>! n

/// See [`std::primitive::u8::funnel_shl`] (and similar for other unsigned integer types)
let impl_11__funnel_shl (x y: usize) (n: u32)
    : Prims.Pure usize (requires n <. impl_11__BITS) (fun _ -> Prims.l_True) =
  if n =. mk_u32 0
  then x
  else
    (impl_11__wrapping_shl x n <: usize) |.
    (impl_11__wrapping_shr y (impl_11__BITS -! n <: u32) <: usize)

/// See [`std::primitive::u8::funnel_shr`] (and similar for other unsigned integer types)
let impl_11__funnel_shr (x y: usize) (n: u32)
    : Prims.Pure usize (requires n <. impl_11__BITS) (fun _ -> Prims.l_True) =
  if n =. mk_u32 0
  then y
  else
    (impl_11__wrapping_shr y n <: usize) |.
    (impl_11__wrapping_shl x (impl_11__BITS -! n <: u32) <: usize)

/// See [`std::primitive::u8::unchecked_disjoint_bitor`] (and similar for other unsigned integer types)
let impl_11__unchecked_disjoint_bitor (x y: usize)
    : Prims.Pure usize (requires (x &. y <: usize) =. mk_usize 0) (fun _ -> Prims.l_True) = x |. y

/// See [`std::primitive::u8::next_power_of_two`] (and similar for other unsigned integer types)
assume
val impl_11__next_power_of_two': x: usize
  -> Prims.Pure usize
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine (mk_i32 2) <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        ((Rust_primitives.Hax.Int.from_machine impl_11__MAX <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine (mk_i32 1) <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True)

unfold
let impl_11__next_power_of_two = impl_11__next_power_of_two'

/// See [`std::primitive::i8::MIN`] (and similar for other signed integer types)
let impl_12__MIN: i8 = mk_i8 (-128)

/// See [`std::primitive::i8::MAX`] (and similar for other signed integer types)
let impl_12__MAX: i8 = mk_i8 127

/// See [`std::primitive::i8::BITS`] (and similar for other signed integer types)
let impl_12__BITS: u32 = mk_u32 8

let impl_12__wrapping_add (x y: i8) : i8 = Rust_primitives.Arithmetic.wrapping_add_i8 x y

/// See [`std::primitive::u8::saturating_add`] (and similar for other integer types)
let impl_12__saturating_add (x y: i8) : i8 = Rust_primitives.Arithmetic.saturating_add_i8 x y

/// See [`std::primitive::u8::overflowing_add`] (and similar for other integer types)
let impl_12__overflowing_add (x y: i8) : (i8 & bool) =
  Rust_primitives.Arithmetic.overflowing_add_i8 x y

/// See [`std::primitive::u8::wrapping_sub`] (and similar for other integer types)
let impl_12__wrapping_sub (x y: i8) : i8 = Rust_primitives.Arithmetic.wrapping_sub_i8 x y

/// See [`std::primitive::u8::saturating_sub`] (and similar for other integer types)
let impl_12__saturating_sub (x y: i8) : i8 = Rust_primitives.Arithmetic.saturating_sub_i8 x y

/// See [`std::primitive::u8::overflowing_sub`] (and similar for other integer types)
let impl_12__overflowing_sub (x y: i8) : (i8 & bool) =
  Rust_primitives.Arithmetic.overflowing_sub_i8 x y

/// See [`std::primitive::u8::wrapping_mul`] (and similar for other integer types)
let impl_12__wrapping_mul (x y: i8) : i8 = Rust_primitives.Arithmetic.wrapping_mul_i8 x y

/// See [`std::primitive::u8::saturating_mul`] (and similar for other integer types)
let impl_12__saturating_mul (x y: i8) : i8 = Rust_primitives.Arithmetic.saturating_mul_i8 x y

/// See [`std::primitive::u8::overflowing_mul`] (and similar for other integer types)
let impl_12__overflowing_mul (x y: i8) : (i8 & bool) =
  Rust_primitives.Arithmetic.overflowing_mul_i8 x y

/// See [`std::primitive::u8::pow`] (and similar for other integer types)
let impl_12__pow (x: i8) (exp: u32) : i8 = Rust_primitives.Arithmetic.pow_i8 x exp

/// See [`std::primitive::u8::overflowing_pow`] (and similar for other integer types)
let impl_12__overflowing_pow (x: i8) (exp: u32) : (i8 & bool) =
  Rust_primitives.Arithmetic.overflowing_pow_i8 x exp

/// See [`std::primitive::u8::count_ones`] (and similar for other integer types)
let impl_12__count_ones (x: i8) : u32 = Rust_primitives.Arithmetic.count_ones_i8 x

/// See [`std::primitive::u8::rotate_right`] (and similar for other integer types)
assume
val impl_12__rotate_right': x: i8 -> n: u32 -> i8

unfold
let impl_12__rotate_right = impl_12__rotate_right'

/// See [`std::primitive::u8::rotate_left`] (and similar for other integer types)
assume
val impl_12__rotate_left': x: i8 -> n: u32 -> i8

unfold
let impl_12__rotate_left = impl_12__rotate_left'

/// See [`std::primitive::u8::leading_zeros`] (and similar for other integer types)
assume
val impl_12__leading_zeros': x: i8 -> u32

unfold
let impl_12__leading_zeros = impl_12__leading_zeros'

/// See [`std::primitive::u8::ilog2`] (and similar for other integer types)
assume
val impl_12__ilog2': x: i8 -> u32

unfold
let impl_12__ilog2 = impl_12__ilog2'

/// See [`std::primitive::u8::from_be_bytes`] (and similar for other integer types)
assume
val impl_12__from_be_bytes': bytes: t_Array u8 (mk_usize 1) -> i8

unfold
let impl_12__from_be_bytes = impl_12__from_be_bytes'

/// See [`std::primitive::u8::from_le_bytes`] (and similar for other integer types)
assume
val impl_12__from_le_bytes': bytes: t_Array u8 (mk_usize 1) -> i8

unfold
let impl_12__from_le_bytes = impl_12__from_le_bytes'

/// See [`std::primitive::u8::to_be_bytes`] (and similar for other integer types)
assume
val impl_12__to_be_bytes': bytes: i8 -> t_Array u8 (mk_usize 1)

unfold
let impl_12__to_be_bytes = impl_12__to_be_bytes'

/// See [`std::primitive::u8::to_le_bytes`] (and similar for other integer types)
assume
val impl_12__to_le_bytes': bytes: i8 -> t_Array u8 (mk_usize 1)

unfold
let impl_12__to_le_bytes = impl_12__to_le_bytes'

/// See [`std::primitive::i8::signum`] (and similar for other signed integer types)
let impl_12__signum (x: i8) : i8 =
  if x >. mk_i8 0 then mk_i8 1 else if x =. mk_i8 0 then mk_i8 0 else mk_i8 (-1)

/// See [`std::primitive::i8::wrapping_neg`] (and similar for other signed integer types)
let impl_12__wrapping_neg (x: i8) : i8 = Rust_primitives.Arithmetic.wrapping_sub_i8 (mk_i8 0) x

/// See [`std::primitive::i8::min_value`] (and similar for other integer types)
let impl_12__min_value (_: Prims.unit) : i8 = impl_12__MIN

/// See [`std::primitive::i8::max_value`] (and similar for other integer types)
let impl_12__max_value (_: Prims.unit) : i8 = impl_12__MAX

/// See [`std::primitive::i8::cast_unsigned`] (and similar for other signed integer types)
let impl_12__cast_unsigned (x: i8) : u8 = cast (x <: i8) <: u8

/// See [`std::primitive::i8::is_positive`] (and similar for other signed integer types)
let impl_12__is_positive (x: i8) : bool = x >. mk_i8 0

/// See [`std::primitive::i8::is_negative`] (and similar for other signed integer types)
let impl_12__is_negative (x: i8) : bool = x <. mk_i8 0

/// See [`std::primitive::i8::count_zeros`] (and similar for other integer types)
let impl_12__count_zeros (x: i8) : u32 = impl_12__BITS -! (impl_12__count_ones x <: u32)

/// See [`std::primitive::i8::overflowing_neg`] (and similar for other integer types)
let impl_12__overflowing_neg (x: i8) : (i8 & bool) =
  if x =. impl_12__MIN
  then impl_12__MIN, true <: (i8 & bool)
  else impl_12__wrapping_neg x, false <: (i8 & bool)

/// See [`std::primitive::i8::saturating_neg`] (and similar for other signed integer types)
let impl_12__saturating_neg (x: i8) : i8 =
  if x =. impl_12__MIN then impl_12__MAX else impl_12__wrapping_neg x

/// See [`std::primitive::i8::wrapping_abs`] (and similar for other signed integer types)
let impl_12__wrapping_abs (x: i8) : i8 = if x <. mk_i8 0 then impl_12__wrapping_neg x else x

/// See [`std::primitive::i8::overflowing_abs`] (and similar for other signed integer types)
let impl_12__overflowing_abs (x: i8) : (i8 & bool) =
  impl_12__wrapping_abs x, x =. impl_12__MIN <: (i8 & bool)

/// See [`std::primitive::i8::saturating_abs`] (and similar for other signed integer types)
let impl_12__saturating_abs (x: i8) : i8 = if x <. mk_i8 0 then impl_12__saturating_neg x else x

/// See [`std::primitive::i8::unsigned_abs`] (and similar for other signed integer types)
let impl_12__unsigned_abs (x: i8) : u8 = cast (impl_12__wrapping_abs x <: i8) <: u8

/// See [`std::primitive::i8::wrapping_pow`] (and similar for other integer types)
let impl_12__wrapping_pow (x: i8) (exp: u32) : i8 =
  let (result: i8), (_: bool) = impl_12__overflowing_pow x exp in
  result

/// See [`std::primitive::i8::saturating_pow`] (and similar for other signed integer types)
let impl_12__saturating_pow (x: i8) (exp: u32) : i8 =
  let (result: i8), (overflowed: bool) = impl_12__overflowing_pow x exp in
  if ~.overflowed
  then result
  else if x <. mk_i8 0 && (exp %! mk_u32 2 <: u32) =. mk_u32 1 then impl_12__MIN else impl_12__MAX

/// See [`std::primitive::i8::abs_diff`] (and similar for other signed integer types)
let impl_12__abs_diff (x y: i8) : u8 =
  if x <. y
  then cast (impl_12__wrapping_sub y x <: i8) <: u8
  else cast (impl_12__wrapping_sub x y <: i8) <: u8

/// See [`std::primitive::i8::midpoint`] (and similar for other signed integer types)
let impl_12__midpoint (x y: i8) : i8 =
  let d:i8 = x ^. y in
  let t:i8 = impl_12__wrapping_add (d >>! mk_i32 1 <: i8) (x &. y <: i8) in
  if t <. mk_i8 0 then impl_12__wrapping_add t (d &. mk_i8 1 <: i8) else t

/// See [`std::primitive::i8::wrapping_add_unsigned`] (and similar for other signed integer types)
let impl_12__wrapping_add_unsigned (x: i8) (y: u8) : i8 =
  impl_12__wrapping_add x (cast (y <: u8) <: i8)

/// See [`std::primitive::i8::wrapping_sub_unsigned`] (and similar for other signed integer types)
let impl_12__wrapping_sub_unsigned (x: i8) (y: u8) : i8 =
  impl_12__wrapping_sub x (cast (y <: u8) <: i8)

/// See [`std::primitive::i8::overflowing_add_unsigned`] (and similar for other signed integer types)
let impl_12__overflowing_add_unsigned (x: i8) (y: u8) : (i8 & bool) =
  let rhs:i8 = cast (y <: u8) <: i8 in
  let (result: i8), (overflowed: bool) = impl_12__overflowing_add x rhs in
  result, overflowed <>. (rhs <. mk_i8 0 <: bool) <: (i8 & bool)

/// See [`std::primitive::i8::overflowing_sub_unsigned`] (and similar for other signed integer types)
let impl_12__overflowing_sub_unsigned (x: i8) (y: u8) : (i8 & bool) =
  let rhs:i8 = cast (y <: u8) <: i8 in
  let (result: i8), (overflowed: bool) = impl_12__overflowing_sub x rhs in
  result, overflowed <>. (rhs <. mk_i8 0 <: bool) <: (i8 & bool)

/// See [`std::primitive::i8::saturating_add_unsigned`] (and similar for other signed integer types)
let impl_12__saturating_add_unsigned (x: i8) (y: u8) : i8 =
  let (result: i8), (overflowed: bool) = impl_12__overflowing_add_unsigned x y in
  if overflowed then impl_12__MAX else result

/// See [`std::primitive::i8::saturating_sub_unsigned`] (and similar for other signed integer types)
let impl_12__saturating_sub_unsigned (x: i8) (y: u8) : i8 =
  let (result: i8), (overflowed: bool) = impl_12__overflowing_sub_unsigned x y in
  if overflowed then impl_12__MIN else result

/// See [`std::primitive::i8::reverse_bits`] (and similar for other signed integer types)
let impl_12__reverse_bits (x: i8) : i8 =
  cast (impl_6__reverse_bits (cast (x <: i8) <: u8) <: u8) <: i8

/// See [`std::primitive::i8::widening_mul`] (and similar for other signed integer types)
let impl_12__widening_mul (x y: i8) : (u8 & i8) =
  let (low: u8), (high: u8) = impl_6__widening_mul (cast (x <: i8) <: u8) (cast (y <: i8) <: u8) in
  let high:i8 = cast (high <: u8) <: i8 in
  let high:i8 = if x <. mk_i8 0 then impl_12__wrapping_sub high y else high in
  let high:i8 = if y <. mk_i8 0 then impl_12__wrapping_sub high x else high in
  low, high <: (u8 & i8)

/// See [`std::primitive::i8::carrying_mul_add`] (and similar for other signed integer types)
let impl_12__carrying_mul_add (x y carry add: i8) : (u8 & i8) =
  let (low: u8), (high: i8) = impl_12__widening_mul x y in
  let (low: u8), (c1: bool) = impl_6__overflowing_add low (cast (carry <: i8) <: u8) in
  let (low: u8), (c2: bool) = impl_6__overflowing_add low (cast (add <: i8) <: u8) in
  let high:i8 = impl_12__wrapping_add high (if c1 then mk_i8 1 else mk_i8 0) in
  let high:i8 = impl_12__wrapping_add high (if c2 then mk_i8 1 else mk_i8 0) in
  let high:i8 =
    impl_12__wrapping_add high (if carry <. mk_i8 0 <: bool then mk_i8 (-1) else mk_i8 0)
  in
  let high:i8 =
    impl_12__wrapping_add high (if add <. mk_i8 0 <: bool then mk_i8 (-1) else mk_i8 0)
  in
  low, high <: (u8 & i8)

/// See [`std::primitive::i8::carrying_mul`] (and similar for other signed integer types)
let impl_12__carrying_mul (x y carry: i8) : (u8 & i8) =
  impl_12__carrying_mul_add x y carry (mk_i8 0)

/// See [`std::primitive::i8::carrying_add`] (and similar for other integer types)
let impl_12__carrying_add (x y: i8) (carry: bool) : (i8 & bool) =
  let (a: i8), (b: bool) = impl_12__overflowing_add x y in
  let (c: i8), (d: bool) = impl_12__overflowing_add a (if carry then mk_i8 1 else mk_i8 0) in
  c, b <>. d <: (i8 & bool)

/// See [`std::primitive::i8::borrowing_sub`] (and similar for other integer types)
let impl_12__borrowing_sub (x y: i8) (borrow: bool) : (i8 & bool) =
  let (a: i8), (b: bool) = impl_12__overflowing_sub x y in
  let (c: i8), (d: bool) = impl_12__overflowing_sub a (if borrow then mk_i8 1 else mk_i8 0) in
  c, b <>. d <: (i8 & bool)

/// See [`std::primitive::i8::trailing_zeros`] (and similar for other integer types)
let impl_12__trailing_zeros (x: i8) : u32 =
  if x =. mk_i8 0
  then impl_12__BITS
  else
    impl_12__count_ones (impl_12__wrapping_sub (x &. (impl_12__wrapping_neg x <: i8) <: i8)
          (mk_i8 1)
        <:
        i8)

/// See [`std::primitive::i8::trailing_ones`] (and similar for other integer types)
let impl_12__trailing_ones (x: i8) : u32 =
  impl_12__trailing_zeros (impl_12__wrapping_sub (mk_i8 (-1)) x <: i8)

/// See [`std::primitive::i8::leading_ones`] (and similar for other integer types)
let impl_12__leading_ones (x: i8) : u32 =
  impl_12__leading_zeros (impl_12__wrapping_sub (mk_i8 (-1)) x <: i8)

/// See [`std::primitive::i8::isolate_lowest_one`] (and similar for other integer types)
let impl_12__isolate_lowest_one (x: i8) : i8 = x &. (impl_12__wrapping_neg x <: i8)

/// See [`std::primitive::i8::swap_bytes`] (and similar for other integer types)
let impl_12__swap_bytes (x: i8) : i8 =
  impl_12__from_le_bytes (impl_12__to_be_bytes x <: t_Array u8 (mk_usize 1))

/// See [`std::primitive::i8::to_be`] (and similar for other integer types)
let impl_12__to_be (x: i8) : i8 = impl_12__swap_bytes x

/// See [`std::primitive::i8::to_le`] (and similar for other integer types)
let impl_12__to_le (x: i8) : i8 = x

/// See [`std::primitive::i8::from_be`] (and similar for other integer types)
let impl_12__from_be (x: i8) : i8 = impl_12__swap_bytes x

/// See [`std::primitive::i8::from_le`] (and similar for other integer types)
let impl_12__from_le (x: i8) : i8 = x

/// See [`std::primitive::i8::to_ne_bytes`] (and similar for other integer types)
let impl_12__to_ne_bytes (x: i8) : t_Array u8 (mk_usize 1) = impl_12__to_le_bytes x

/// See [`std::primitive::i8::from_ne_bytes`] (and similar for other integer types)
let impl_12__from_ne_bytes (bytes: t_Array u8 (mk_usize 1)) : i8 = impl_12__from_le_bytes bytes

/// See [`std::primitive::i8::wrapping_shl`] (and similar for other integer types)
let impl_12__wrapping_shl (x: i8) (n: u32) : i8 = x <<! (n %! impl_12__BITS <: u32)

/// See [`std::primitive::i8::wrapping_shr`] (and similar for other integer types)
let impl_12__wrapping_shr (x: i8) (n: u32) : i8 = x >>! (n %! impl_12__BITS <: u32)

/// See [`std::primitive::i8::isolate_highest_one`] (and similar for other integer types)
let impl_12__isolate_highest_one (x: i8) : i8 =
  x &. (impl_12__wrapping_shr impl_12__MIN (impl_12__leading_zeros x <: u32) <: i8)

/// See [`std::primitive::i8::overflowing_shl`] (and similar for other integer types)
let impl_12__overflowing_shl (x: i8) (n: u32) : (i8 & bool) =
  impl_12__wrapping_shl x n, n >=. impl_12__BITS <: (i8 & bool)

/// See [`std::primitive::i8::overflowing_shr`] (and similar for other integer types)
let impl_12__overflowing_shr (x: i8) (n: u32) : (i8 & bool) =
  impl_12__wrapping_shr x n, n >=. impl_12__BITS <: (i8 & bool)

/// See [`std::primitive::i8::unbounded_shl`] (and similar for other integer types)
let impl_12__unbounded_shl (x: i8) (n: u32) : i8 = if n <. impl_12__BITS then x <<! n else mk_i8 0

/// See [`std::primitive::i8::unbounded_shr`] (and similar for other signed integer types)
let impl_12__unbounded_shr (x: i8) (n: u32) : i8 =
  if n <. impl_12__BITS then x >>! n else x >>! (impl_12__BITS -! mk_u32 1 <: u32)

/// See [`std::primitive::i8::clamp_magnitude`] (and similar for other signed integer types)
let impl_12__clamp_magnitude (x: i8) (limit: u8) : i8 =
  if limit >. (cast (impl_12__MAX <: i8) <: u8)
  then x
  else
    let hi:i8 = cast (limit <: u8) <: i8 in
    let lo:i8 = impl_12__wrapping_neg hi in
    if x <. lo then lo else if x >. hi then hi else x

/// See [`std::primitive::u8::unchecked_add`] (and similar for other integer types)
let impl_12__unchecked_add (x y: i8)
    : Prims.Pure i8
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_12__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_12__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) = x +! y

/// See [`std::primitive::u8::unchecked_sub`] (and similar for other integer types)
let impl_12__unchecked_sub (x y: i8)
    : Prims.Pure i8
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_12__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_12__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) = x -! y

/// See [`std::primitive::u8::unchecked_mul`] (and similar for other integer types)
let impl_12__unchecked_mul (x y: i8)
    : Prims.Pure i8
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_12__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_12__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) = x *! y

/// See [`std::primitive::u8::rem_euclid`] (and similar for other integer types)
let impl_12__rem_euclid (x y: i8)
    : Prims.Pure i8
      (requires y <>. mk_i8 0 && ~.((x =. impl_12__MIN <: bool) && (y =. mk_i8 (-1) <: bool)))
      (fun _ -> Prims.l_True) = Rust_primitives.Arithmetic.rem_euclid_i8 x y

/// See [`std::primitive::i8::abs`] (and similar for other signed integer types)
let impl_12__abs (x: i8) : Prims.Pure i8 (requires x >. impl_12__MIN) (fun _ -> Prims.l_True) =
  Rust_primitives.Arithmetic.abs_i8 x

/// See [`std::primitive::u8::unchecked_div`] (and similar for other integer types)
let impl_12__unchecked_div (x y: i8)
    : Prims.Pure i8
      (requires y <>. mk_i8 0 && (x <>. impl_12__MIN || y <>. mk_i8 (-1)))
      (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::unchecked_rem`] (and similar for other integer types)
let impl_12__unchecked_rem (x y: i8)
    : Prims.Pure i8
      (requires y <>. mk_i8 0 && (x <>. impl_12__MIN || y <>. mk_i8 (-1)))
      (fun _ -> Prims.l_True) = x %! y

/// See [`std::primitive::i8::div_ceil`] (and similar for other signed integer types)
let impl_12__div_ceil (x y: i8)
    : Prims.Pure i8
      (requires y <>. mk_i8 0 && ~.((x =. impl_12__MIN <: bool) && (y =. mk_i8 (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let d:i8 = x /! y in
  let r:i8 = x %! y in
  if r >. mk_i8 0 && y >. mk_i8 0 || r <. mk_i8 0 && y <. mk_i8 0 then d +! mk_i8 1 else d

/// See [`std::primitive::i8::strict_neg`] (and similar for other integer types)
let impl_12__strict_neg (x: i8)
    : Prims.Pure i8 (requires x <>. impl_12__MIN) (fun _ -> Prims.l_True) =
  if x =. impl_12__MIN then Core_models.Panicking.Internal.panic #i8 () else impl_12__wrapping_neg x

/// See [`std::primitive::i8::unchecked_neg`] (and similar for other signed integer types)
let impl_12__unchecked_neg (x: i8)
    : Prims.Pure i8 (requires x <>. impl_12__MIN) (fun _ -> Prims.l_True) = mk_i8 0 -! x

/// See [`std::primitive::i8::strict_abs`] (and similar for other signed integer types)
let impl_12__strict_abs (x: i8)
    : Prims.Pure i8 (requires x <>. impl_12__MIN) (fun _ -> Prims.l_True) =
  if x <. mk_i8 0 then impl_12__strict_neg x else x

/// See [`std::primitive::i8::strict_pow`] (and similar for other integer types)
let impl_12__strict_pow (x: i8) (exp: u32)
    : Prims.Pure i8
      (requires (impl_12__overflowing_pow x exp <: (i8 & bool))._2 =. false)
      (fun _ -> Prims.l_True) =
  let (result: i8), (overflowed: bool) = impl_12__overflowing_pow x exp in
  if overflowed then Core_models.Panicking.Internal.panic #i8 () else result

/// See [`std::primitive::i8::strict_add`] (and similar for other integer types)
let impl_12__strict_add (x y: i8)
    : Prims.Pure i8
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_12__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_12__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: i8), (overflowed: bool) = impl_12__overflowing_add x y in
  if overflowed then Core_models.Panicking.Internal.panic #i8 () else result

/// See [`std::primitive::i8::strict_sub`] (and similar for other integer types)
let impl_12__strict_sub (x y: i8)
    : Prims.Pure i8
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_12__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_12__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: i8), (overflowed: bool) = impl_12__overflowing_sub x y in
  if overflowed then Core_models.Panicking.Internal.panic #i8 () else result

/// See [`std::primitive::i8::strict_mul`] (and similar for other integer types)
let impl_12__strict_mul (x y: i8)
    : Prims.Pure i8
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_12__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_12__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: i8), (overflowed: bool) = impl_12__overflowing_mul x y in
  if overflowed then Core_models.Panicking.Internal.panic #i8 () else result

/// See [`std::primitive::i8::overflowing_div`] (and similar for other signed integer types)
let impl_12__overflowing_div (x y: i8)
    : Prims.Pure (i8 & bool) (requires y <>. mk_i8 0) (fun _ -> Prims.l_True) =
  if x =. impl_12__MIN && y =. mk_i8 (-1)
  then x, true <: (i8 & bool)
  else x /! y, false <: (i8 & bool)

/// See [`std::primitive::i8::overflowing_rem`] (and similar for other signed integer types)
let impl_12__overflowing_rem (x y: i8)
    : Prims.Pure (i8 & bool) (requires y <>. mk_i8 0) (fun _ -> Prims.l_True) =
  if y =. mk_i8 (-1)
  then mk_i8 0, x =. impl_12__MIN <: (i8 & bool)
  else x %! y, false <: (i8 & bool)

/// See [`std::primitive::i8::wrapping_div`] (and similar for other signed integer types)
let impl_12__wrapping_div (x y: i8) : Prims.Pure i8 (requires y <>. mk_i8 0) (fun _ -> Prims.l_True) =
  let (result: i8), (_: bool) = impl_12__overflowing_div x y in
  result

/// See [`std::primitive::i8::wrapping_rem`] (and similar for other signed integer types)
let impl_12__wrapping_rem (x y: i8) : Prims.Pure i8 (requires y <>. mk_i8 0) (fun _ -> Prims.l_True) =
  let (result: i8), (_: bool) = impl_12__overflowing_rem x y in
  result

/// See [`std::primitive::i8::saturating_div`] (and similar for other signed integer types)
let impl_12__saturating_div (x y: i8)
    : Prims.Pure i8 (requires y <>. mk_i8 0) (fun _ -> Prims.l_True) =
  let (result: i8), (overflowed: bool) = impl_12__overflowing_div x y in
  if overflowed then impl_12__MAX else result

/// See [`std::primitive::i8::strict_div`] (and similar for other signed integer types)
let impl_12__strict_div (x y: i8)
    : Prims.Pure i8
      (requires y <>. mk_i8 0 && ~.((x =. impl_12__MIN <: bool) && (y =. mk_i8 (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let (result: i8), (overflowed: bool) = impl_12__overflowing_div x y in
  if overflowed then Core_models.Panicking.Internal.panic #i8 () else result

/// See [`std::primitive::i8::strict_rem`] (and similar for other signed integer types)
let impl_12__strict_rem (x y: i8)
    : Prims.Pure i8
      (requires y <>. mk_i8 0 && ~.((x =. impl_12__MIN <: bool) && (y =. mk_i8 (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let (result: i8), (overflowed: bool) = impl_12__overflowing_rem x y in
  if overflowed then Core_models.Panicking.Internal.panic #i8 () else result

/// See [`std::primitive::i8::div_euclid`] (and similar for other signed integer types)
let impl_12__div_euclid (x y: i8)
    : Prims.Pure i8
      (requires y <>. mk_i8 0 && ~.((x =. impl_12__MIN <: bool) && (y =. mk_i8 (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let q:i8 = x /! y in
  if (x %! y <: i8) <. mk_i8 0
  then if y >. mk_i8 0 then impl_12__wrapping_sub q (mk_i8 1) else impl_12__wrapping_add q (mk_i8 1)
  else q

/// See [`std::primitive::i8::overflowing_div_euclid`] (and similar for other signed integer types)
let impl_12__overflowing_div_euclid (x y: i8)
    : Prims.Pure (i8 & bool) (requires y <>. mk_i8 0) (fun _ -> Prims.l_True) =
  if x =. impl_12__MIN && y =. mk_i8 (-1)
  then x, true <: (i8 & bool)
  else impl_12__div_euclid x y, false <: (i8 & bool)

/// See [`std::primitive::i8::wrapping_div_euclid`] (and similar for other signed integer types)
let impl_12__wrapping_div_euclid (x y: i8)
    : Prims.Pure i8 (requires y <>. mk_i8 0) (fun _ -> Prims.l_True) =
  let (result: i8), (_: bool) = impl_12__overflowing_div_euclid x y in
  result

/// See [`std::primitive::i8::strict_div_euclid`] (and similar for other signed integer types)
let impl_12__strict_div_euclid (x y: i8)
    : Prims.Pure i8
      (requires y <>. mk_i8 0 && ~.((x =. impl_12__MIN <: bool) && (y =. mk_i8 (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let (result: i8), (overflowed: bool) = impl_12__overflowing_div_euclid x y in
  if overflowed then Core_models.Panicking.Internal.panic #i8 () else result

/// See [`std::primitive::i8::overflowing_rem_euclid`] (and similar for other signed integer types)
let impl_12__overflowing_rem_euclid (x y: i8)
    : Prims.Pure (i8 & bool) (requires y <>. mk_i8 0) (fun _ -> Prims.l_True) =
  if y =. mk_i8 (-1)
  then mk_i8 0, x =. impl_12__MIN <: (i8 & bool)
  else impl_12__rem_euclid x y, false <: (i8 & bool)

/// See [`std::primitive::i8::wrapping_rem_euclid`] (and similar for other signed integer types)
let impl_12__wrapping_rem_euclid (x y: i8)
    : Prims.Pure i8 (requires y <>. mk_i8 0) (fun _ -> Prims.l_True) =
  let (result: i8), (_: bool) = impl_12__overflowing_rem_euclid x y in
  result

/// See [`std::primitive::i8::strict_rem_euclid`] (and similar for other signed integer types)
let impl_12__strict_rem_euclid (x y: i8)
    : Prims.Pure i8
      (requires y <>. mk_i8 0 && ~.((x =. impl_12__MIN <: bool) && (y =. mk_i8 (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let (result: i8), (overflowed: bool) = impl_12__overflowing_rem_euclid x y in
  if overflowed then Core_models.Panicking.Internal.panic #i8 () else result

/// See [`std::primitive::i8::div_floor`] (and similar for other signed integer types)
let impl_12__div_floor (x y: i8)
    : Prims.Pure i8
      (requires y <>. mk_i8 0 && ~.((x =. impl_12__MIN <: bool) && (y =. mk_i8 (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let d:i8 = x /! y in
  let r:i8 = x %! y in
  if r <>. mk_i8 0 && (x <. mk_i8 0 <: bool) <>. (y <. mk_i8 0 <: bool)
  then impl_12__wrapping_sub d (mk_i8 1)
  else d

/// See [`std::primitive::i8::unchecked_div_exact`] (and similar for other signed integer types)
let impl_12__unchecked_div_exact (x y: i8)
    : Prims.Pure i8 (requires y >. mk_i8 0 && (x %! y <: i8) =. mk_i8 0) (fun _ -> Prims.l_True) =
  x /! y

/// See [`std::primitive::i8::strict_add_unsigned`] (and similar for other signed integer types)
let impl_12__strict_add_unsigned (x: i8) (y: u8)
    : Prims.Pure i8
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_12__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: i8), (overflowed: bool) = impl_12__overflowing_add_unsigned x y in
  if overflowed then Core_models.Panicking.Internal.panic #i8 () else result

/// See [`std::primitive::i8::strict_sub_unsigned`] (and similar for other signed integer types)
let impl_12__strict_sub_unsigned (x: i8) (y: u8)
    : Prims.Pure i8
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_12__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: i8), (overflowed: bool) = impl_12__overflowing_sub_unsigned x y in
  if overflowed then Core_models.Panicking.Internal.panic #i8 () else result

/// See [`std::primitive::i8::strict_shl`] (and similar for other integer types)
let impl_12__strict_shl (x: i8) (n: u32)
    : Prims.Pure i8 (requires n <. impl_12__BITS) (fun _ -> Prims.l_True) =
  if n <. impl_12__BITS then x <<! n else Core_models.Panicking.Internal.panic #i8 ()

/// See [`std::primitive::i8::strict_shr`] (and similar for other integer types)
let impl_12__strict_shr (x: i8) (n: u32)
    : Prims.Pure i8 (requires n <. impl_12__BITS) (fun _ -> Prims.l_True) =
  if n <. impl_12__BITS then x >>! n else Core_models.Panicking.Internal.panic #i8 ()

/// See [`std::primitive::i8::unchecked_shl`] (and similar for other integer types)
let impl_12__unchecked_shl (x: i8) (n: u32)
    : Prims.Pure i8 (requires n <. impl_12__BITS) (fun _ -> Prims.l_True) = x <<! n

/// See [`std::primitive::i8::unchecked_shr`] (and similar for other integer types)
let impl_12__unchecked_shr (x: i8) (n: u32)
    : Prims.Pure i8 (requires n <. impl_12__BITS) (fun _ -> Prims.l_True) = x >>! n

/// See [`std::primitive::i8::unchecked_shl_exact`] (and similar for other signed integer types)
let impl_12__unchecked_shl_exact (x: i8) (n: u32)
    : Prims.Pure i8
      (requires
        (n <. (impl_12__leading_zeros x <: u32) || n <. (impl_12__leading_ones x <: u32)) &&
        n <. impl_12__BITS)
      (fun _ -> Prims.l_True) = x <<! n

/// See [`std::primitive::i8::unchecked_shr_exact`] (and similar for other integer types)
let impl_12__unchecked_shr_exact (x: i8) (n: u32)
    : Prims.Pure i8
      (requires n <=. (impl_12__trailing_zeros x <: u32) && n <. impl_12__BITS)
      (fun _ -> Prims.l_True) = x >>! n

/// See [`std::primitive::i8::MIN`] (and similar for other signed integer types)
let impl_13__MIN: i16 = mk_i16 (-32768)

/// See [`std::primitive::i8::MAX`] (and similar for other signed integer types)
let impl_13__MAX: i16 = mk_i16 32767

/// See [`std::primitive::i8::BITS`] (and similar for other signed integer types)
let impl_13__BITS: u32 = mk_u32 16

let impl_13__wrapping_add (x y: i16) : i16 = Rust_primitives.Arithmetic.wrapping_add_i16 x y

/// See [`std::primitive::u8::saturating_add`] (and similar for other integer types)
let impl_13__saturating_add (x y: i16) : i16 = Rust_primitives.Arithmetic.saturating_add_i16 x y

/// See [`std::primitive::u8::overflowing_add`] (and similar for other integer types)
let impl_13__overflowing_add (x y: i16) : (i16 & bool) =
  Rust_primitives.Arithmetic.overflowing_add_i16 x y

/// See [`std::primitive::u8::wrapping_sub`] (and similar for other integer types)
let impl_13__wrapping_sub (x y: i16) : i16 = Rust_primitives.Arithmetic.wrapping_sub_i16 x y

/// See [`std::primitive::u8::saturating_sub`] (and similar for other integer types)
let impl_13__saturating_sub (x y: i16) : i16 = Rust_primitives.Arithmetic.saturating_sub_i16 x y

/// See [`std::primitive::u8::overflowing_sub`] (and similar for other integer types)
let impl_13__overflowing_sub (x y: i16) : (i16 & bool) =
  Rust_primitives.Arithmetic.overflowing_sub_i16 x y

/// See [`std::primitive::u8::wrapping_mul`] (and similar for other integer types)
let impl_13__wrapping_mul (x y: i16) : i16 = Rust_primitives.Arithmetic.wrapping_mul_i16 x y

/// See [`std::primitive::u8::saturating_mul`] (and similar for other integer types)
let impl_13__saturating_mul (x y: i16) : i16 = Rust_primitives.Arithmetic.saturating_mul_i16 x y

/// See [`std::primitive::u8::overflowing_mul`] (and similar for other integer types)
let impl_13__overflowing_mul (x y: i16) : (i16 & bool) =
  Rust_primitives.Arithmetic.overflowing_mul_i16 x y

/// See [`std::primitive::u8::pow`] (and similar for other integer types)
let impl_13__pow (x: i16) (exp: u32) : i16 = Rust_primitives.Arithmetic.pow_i16 x exp

/// See [`std::primitive::u8::overflowing_pow`] (and similar for other integer types)
let impl_13__overflowing_pow (x: i16) (exp: u32) : (i16 & bool) =
  Rust_primitives.Arithmetic.overflowing_pow_i16 x exp

/// See [`std::primitive::u8::count_ones`] (and similar for other integer types)
let impl_13__count_ones (x: i16) : u32 = Rust_primitives.Arithmetic.count_ones_i16 x

/// See [`std::primitive::u8::rotate_right`] (and similar for other integer types)
assume
val impl_13__rotate_right': x: i16 -> n: u32 -> i16

unfold
let impl_13__rotate_right = impl_13__rotate_right'

/// See [`std::primitive::u8::rotate_left`] (and similar for other integer types)
assume
val impl_13__rotate_left': x: i16 -> n: u32 -> i16

unfold
let impl_13__rotate_left = impl_13__rotate_left'

/// See [`std::primitive::u8::leading_zeros`] (and similar for other integer types)
assume
val impl_13__leading_zeros': x: i16 -> u32

unfold
let impl_13__leading_zeros = impl_13__leading_zeros'

/// See [`std::primitive::u8::ilog2`] (and similar for other integer types)
assume
val impl_13__ilog2': x: i16 -> u32

unfold
let impl_13__ilog2 = impl_13__ilog2'

/// See [`std::primitive::u8::from_be_bytes`] (and similar for other integer types)
assume
val impl_13__from_be_bytes': bytes: t_Array u8 (mk_usize 2) -> i16

unfold
let impl_13__from_be_bytes = impl_13__from_be_bytes'

/// See [`std::primitive::u8::from_le_bytes`] (and similar for other integer types)
assume
val impl_13__from_le_bytes': bytes: t_Array u8 (mk_usize 2) -> i16

unfold
let impl_13__from_le_bytes = impl_13__from_le_bytes'

/// See [`std::primitive::u8::to_be_bytes`] (and similar for other integer types)
assume
val impl_13__to_be_bytes': bytes: i16 -> t_Array u8 (mk_usize 2)

unfold
let impl_13__to_be_bytes = impl_13__to_be_bytes'

/// See [`std::primitive::u8::to_le_bytes`] (and similar for other integer types)
assume
val impl_13__to_le_bytes': bytes: i16 -> t_Array u8 (mk_usize 2)

unfold
let impl_13__to_le_bytes = impl_13__to_le_bytes'

/// See [`std::primitive::i8::signum`] (and similar for other signed integer types)
let impl_13__signum (x: i16) : i16 =
  if x >. mk_i16 0 then mk_i16 1 else if x =. mk_i16 0 then mk_i16 0 else mk_i16 (-1)

/// See [`std::primitive::i8::wrapping_neg`] (and similar for other signed integer types)
let impl_13__wrapping_neg (x: i16) : i16 = Rust_primitives.Arithmetic.wrapping_sub_i16 (mk_i16 0) x

/// See [`std::primitive::i8::min_value`] (and similar for other integer types)
let impl_13__min_value (_: Prims.unit) : i16 = impl_13__MIN

/// See [`std::primitive::i8::max_value`] (and similar for other integer types)
let impl_13__max_value (_: Prims.unit) : i16 = impl_13__MAX

/// See [`std::primitive::i8::cast_unsigned`] (and similar for other signed integer types)
let impl_13__cast_unsigned (x: i16) : u16 = cast (x <: i16) <: u16

/// See [`std::primitive::i8::is_positive`] (and similar for other signed integer types)
let impl_13__is_positive (x: i16) : bool = x >. mk_i16 0

/// See [`std::primitive::i8::is_negative`] (and similar for other signed integer types)
let impl_13__is_negative (x: i16) : bool = x <. mk_i16 0

/// See [`std::primitive::i8::count_zeros`] (and similar for other integer types)
let impl_13__count_zeros (x: i16) : u32 = impl_13__BITS -! (impl_13__count_ones x <: u32)

/// See [`std::primitive::i8::overflowing_neg`] (and similar for other integer types)
let impl_13__overflowing_neg (x: i16) : (i16 & bool) =
  if x =. impl_13__MIN
  then impl_13__MIN, true <: (i16 & bool)
  else impl_13__wrapping_neg x, false <: (i16 & bool)

/// See [`std::primitive::i8::saturating_neg`] (and similar for other signed integer types)
let impl_13__saturating_neg (x: i16) : i16 =
  if x =. impl_13__MIN then impl_13__MAX else impl_13__wrapping_neg x

/// See [`std::primitive::i8::wrapping_abs`] (and similar for other signed integer types)
let impl_13__wrapping_abs (x: i16) : i16 = if x <. mk_i16 0 then impl_13__wrapping_neg x else x

/// See [`std::primitive::i8::overflowing_abs`] (and similar for other signed integer types)
let impl_13__overflowing_abs (x: i16) : (i16 & bool) =
  impl_13__wrapping_abs x, x =. impl_13__MIN <: (i16 & bool)

/// See [`std::primitive::i8::saturating_abs`] (and similar for other signed integer types)
let impl_13__saturating_abs (x: i16) : i16 = if x <. mk_i16 0 then impl_13__saturating_neg x else x

/// See [`std::primitive::i8::unsigned_abs`] (and similar for other signed integer types)
let impl_13__unsigned_abs (x: i16) : u16 = cast (impl_13__wrapping_abs x <: i16) <: u16

/// See [`std::primitive::i8::wrapping_pow`] (and similar for other integer types)
let impl_13__wrapping_pow (x: i16) (exp: u32) : i16 =
  let (result: i16), (_: bool) = impl_13__overflowing_pow x exp in
  result

/// See [`std::primitive::i8::saturating_pow`] (and similar for other signed integer types)
let impl_13__saturating_pow (x: i16) (exp: u32) : i16 =
  let (result: i16), (overflowed: bool) = impl_13__overflowing_pow x exp in
  if ~.overflowed
  then result
  else if x <. mk_i16 0 && (exp %! mk_u32 2 <: u32) =. mk_u32 1 then impl_13__MIN else impl_13__MAX

/// See [`std::primitive::i8::abs_diff`] (and similar for other signed integer types)
let impl_13__abs_diff (x y: i16) : u16 =
  if x <. y
  then cast (impl_13__wrapping_sub y x <: i16) <: u16
  else cast (impl_13__wrapping_sub x y <: i16) <: u16

/// See [`std::primitive::i8::midpoint`] (and similar for other signed integer types)
let impl_13__midpoint (x y: i16) : i16 =
  let d:i16 = x ^. y in
  let t:i16 = impl_13__wrapping_add (d >>! mk_i32 1 <: i16) (x &. y <: i16) in
  if t <. mk_i16 0 then impl_13__wrapping_add t (d &. mk_i16 1 <: i16) else t

/// See [`std::primitive::i8::wrapping_add_unsigned`] (and similar for other signed integer types)
let impl_13__wrapping_add_unsigned (x: i16) (y: u16) : i16 =
  impl_13__wrapping_add x (cast (y <: u16) <: i16)

/// See [`std::primitive::i8::wrapping_sub_unsigned`] (and similar for other signed integer types)
let impl_13__wrapping_sub_unsigned (x: i16) (y: u16) : i16 =
  impl_13__wrapping_sub x (cast (y <: u16) <: i16)

/// See [`std::primitive::i8::overflowing_add_unsigned`] (and similar for other signed integer types)
let impl_13__overflowing_add_unsigned (x: i16) (y: u16) : (i16 & bool) =
  let rhs:i16 = cast (y <: u16) <: i16 in
  let (result: i16), (overflowed: bool) = impl_13__overflowing_add x rhs in
  result, overflowed <>. (rhs <. mk_i16 0 <: bool) <: (i16 & bool)

/// See [`std::primitive::i8::overflowing_sub_unsigned`] (and similar for other signed integer types)
let impl_13__overflowing_sub_unsigned (x: i16) (y: u16) : (i16 & bool) =
  let rhs:i16 = cast (y <: u16) <: i16 in
  let (result: i16), (overflowed: bool) = impl_13__overflowing_sub x rhs in
  result, overflowed <>. (rhs <. mk_i16 0 <: bool) <: (i16 & bool)

/// See [`std::primitive::i8::saturating_add_unsigned`] (and similar for other signed integer types)
let impl_13__saturating_add_unsigned (x: i16) (y: u16) : i16 =
  let (result: i16), (overflowed: bool) = impl_13__overflowing_add_unsigned x y in
  if overflowed then impl_13__MAX else result

/// See [`std::primitive::i8::saturating_sub_unsigned`] (and similar for other signed integer types)
let impl_13__saturating_sub_unsigned (x: i16) (y: u16) : i16 =
  let (result: i16), (overflowed: bool) = impl_13__overflowing_sub_unsigned x y in
  if overflowed then impl_13__MIN else result

/// See [`std::primitive::i8::reverse_bits`] (and similar for other signed integer types)
let impl_13__reverse_bits (x: i16) : i16 =
  cast (impl_7__reverse_bits (cast (x <: i16) <: u16) <: u16) <: i16

/// See [`std::primitive::i8::widening_mul`] (and similar for other signed integer types)
let impl_13__widening_mul (x y: i16) : (u16 & i16) =
  let (low: u16), (high: u16) =
    impl_7__widening_mul (cast (x <: i16) <: u16) (cast (y <: i16) <: u16)
  in
  let high:i16 = cast (high <: u16) <: i16 in
  let high:i16 = if x <. mk_i16 0 then impl_13__wrapping_sub high y else high in
  let high:i16 = if y <. mk_i16 0 then impl_13__wrapping_sub high x else high in
  low, high <: (u16 & i16)

/// See [`std::primitive::i8::carrying_mul_add`] (and similar for other signed integer types)
let impl_13__carrying_mul_add (x y carry add: i16) : (u16 & i16) =
  let (low: u16), (high: i16) = impl_13__widening_mul x y in
  let (low: u16), (c1: bool) = impl_7__overflowing_add low (cast (carry <: i16) <: u16) in
  let (low: u16), (c2: bool) = impl_7__overflowing_add low (cast (add <: i16) <: u16) in
  let high:i16 = impl_13__wrapping_add high (if c1 then mk_i16 1 else mk_i16 0) in
  let high:i16 = impl_13__wrapping_add high (if c2 then mk_i16 1 else mk_i16 0) in
  let high:i16 =
    impl_13__wrapping_add high (if carry <. mk_i16 0 <: bool then mk_i16 (-1) else mk_i16 0)
  in
  let high:i16 =
    impl_13__wrapping_add high (if add <. mk_i16 0 <: bool then mk_i16 (-1) else mk_i16 0)
  in
  low, high <: (u16 & i16)

/// See [`std::primitive::i8::carrying_mul`] (and similar for other signed integer types)
let impl_13__carrying_mul (x y carry: i16) : (u16 & i16) =
  impl_13__carrying_mul_add x y carry (mk_i16 0)

/// See [`std::primitive::i8::carrying_add`] (and similar for other integer types)
let impl_13__carrying_add (x y: i16) (carry: bool) : (i16 & bool) =
  let (a: i16), (b: bool) = impl_13__overflowing_add x y in
  let (c: i16), (d: bool) = impl_13__overflowing_add a (if carry then mk_i16 1 else mk_i16 0) in
  c, b <>. d <: (i16 & bool)

/// See [`std::primitive::i8::borrowing_sub`] (and similar for other integer types)
let impl_13__borrowing_sub (x y: i16) (borrow: bool) : (i16 & bool) =
  let (a: i16), (b: bool) = impl_13__overflowing_sub x y in
  let (c: i16), (d: bool) = impl_13__overflowing_sub a (if borrow then mk_i16 1 else mk_i16 0) in
  c, b <>. d <: (i16 & bool)

/// See [`std::primitive::i8::trailing_zeros`] (and similar for other integer types)
let impl_13__trailing_zeros (x: i16) : u32 =
  if x =. mk_i16 0
  then impl_13__BITS
  else
    impl_13__count_ones (impl_13__wrapping_sub (x &. (impl_13__wrapping_neg x <: i16) <: i16)
          (mk_i16 1)
        <:
        i16)

/// See [`std::primitive::i8::trailing_ones`] (and similar for other integer types)
let impl_13__trailing_ones (x: i16) : u32 =
  impl_13__trailing_zeros (impl_13__wrapping_sub (mk_i16 (-1)) x <: i16)

/// See [`std::primitive::i8::leading_ones`] (and similar for other integer types)
let impl_13__leading_ones (x: i16) : u32 =
  impl_13__leading_zeros (impl_13__wrapping_sub (mk_i16 (-1)) x <: i16)

/// See [`std::primitive::i8::isolate_lowest_one`] (and similar for other integer types)
let impl_13__isolate_lowest_one (x: i16) : i16 = x &. (impl_13__wrapping_neg x <: i16)

/// See [`std::primitive::i8::swap_bytes`] (and similar for other integer types)
let impl_13__swap_bytes (x: i16) : i16 =
  impl_13__from_le_bytes (impl_13__to_be_bytes x <: t_Array u8 (mk_usize 2))

/// See [`std::primitive::i8::to_be`] (and similar for other integer types)
let impl_13__to_be (x: i16) : i16 = impl_13__swap_bytes x

/// See [`std::primitive::i8::to_le`] (and similar for other integer types)
let impl_13__to_le (x: i16) : i16 = x

/// See [`std::primitive::i8::from_be`] (and similar for other integer types)
let impl_13__from_be (x: i16) : i16 = impl_13__swap_bytes x

/// See [`std::primitive::i8::from_le`] (and similar for other integer types)
let impl_13__from_le (x: i16) : i16 = x

/// See [`std::primitive::i8::to_ne_bytes`] (and similar for other integer types)
let impl_13__to_ne_bytes (x: i16) : t_Array u8 (mk_usize 2) = impl_13__to_le_bytes x

/// See [`std::primitive::i8::from_ne_bytes`] (and similar for other integer types)
let impl_13__from_ne_bytes (bytes: t_Array u8 (mk_usize 2)) : i16 = impl_13__from_le_bytes bytes

/// See [`std::primitive::i8::wrapping_shl`] (and similar for other integer types)
let impl_13__wrapping_shl (x: i16) (n: u32) : i16 = x <<! (n %! impl_13__BITS <: u32)

/// See [`std::primitive::i8::wrapping_shr`] (and similar for other integer types)
let impl_13__wrapping_shr (x: i16) (n: u32) : i16 = x >>! (n %! impl_13__BITS <: u32)

/// See [`std::primitive::i8::isolate_highest_one`] (and similar for other integer types)
let impl_13__isolate_highest_one (x: i16) : i16 =
  x &. (impl_13__wrapping_shr impl_13__MIN (impl_13__leading_zeros x <: u32) <: i16)

/// See [`std::primitive::i8::overflowing_shl`] (and similar for other integer types)
let impl_13__overflowing_shl (x: i16) (n: u32) : (i16 & bool) =
  impl_13__wrapping_shl x n, n >=. impl_13__BITS <: (i16 & bool)

/// See [`std::primitive::i8::overflowing_shr`] (and similar for other integer types)
let impl_13__overflowing_shr (x: i16) (n: u32) : (i16 & bool) =
  impl_13__wrapping_shr x n, n >=. impl_13__BITS <: (i16 & bool)

/// See [`std::primitive::i8::unbounded_shl`] (and similar for other integer types)
let impl_13__unbounded_shl (x: i16) (n: u32) : i16 =
  if n <. impl_13__BITS then x <<! n else mk_i16 0

/// See [`std::primitive::i8::unbounded_shr`] (and similar for other signed integer types)
let impl_13__unbounded_shr (x: i16) (n: u32) : i16 =
  if n <. impl_13__BITS then x >>! n else x >>! (impl_13__BITS -! mk_u32 1 <: u32)

/// See [`std::primitive::i8::clamp_magnitude`] (and similar for other signed integer types)
let impl_13__clamp_magnitude (x: i16) (limit: u16) : i16 =
  if limit >. (cast (impl_13__MAX <: i16) <: u16)
  then x
  else
    let hi:i16 = cast (limit <: u16) <: i16 in
    let lo:i16 = impl_13__wrapping_neg hi in
    if x <. lo then lo else if x >. hi then hi else x

/// See [`std::primitive::u8::unchecked_add`] (and similar for other integer types)
let impl_13__unchecked_add (x y: i16)
    : Prims.Pure i16
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_13__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_13__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) = x +! y

/// See [`std::primitive::u8::unchecked_sub`] (and similar for other integer types)
let impl_13__unchecked_sub (x y: i16)
    : Prims.Pure i16
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_13__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_13__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) = x -! y

/// See [`std::primitive::u8::unchecked_mul`] (and similar for other integer types)
let impl_13__unchecked_mul (x y: i16)
    : Prims.Pure i16
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_13__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_13__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) = x *! y

/// See [`std::primitive::u8::rem_euclid`] (and similar for other integer types)
let impl_13__rem_euclid (x y: i16)
    : Prims.Pure i16
      (requires y <>. mk_i16 0 && ~.((x =. impl_13__MIN <: bool) && (y =. mk_i16 (-1) <: bool)))
      (fun _ -> Prims.l_True) = Rust_primitives.Arithmetic.rem_euclid_i16 x y

/// See [`std::primitive::i8::abs`] (and similar for other signed integer types)
let impl_13__abs (x: i16) : Prims.Pure i16 (requires x >. impl_13__MIN) (fun _ -> Prims.l_True) =
  Rust_primitives.Arithmetic.abs_i16 x

/// See [`std::primitive::u8::unchecked_div`] (and similar for other integer types)
let impl_13__unchecked_div (x y: i16)
    : Prims.Pure i16
      (requires y <>. mk_i16 0 && (x <>. impl_13__MIN || y <>. mk_i16 (-1)))
      (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::unchecked_rem`] (and similar for other integer types)
let impl_13__unchecked_rem (x y: i16)
    : Prims.Pure i16
      (requires y <>. mk_i16 0 && (x <>. impl_13__MIN || y <>. mk_i16 (-1)))
      (fun _ -> Prims.l_True) = x %! y

/// See [`std::primitive::i8::div_ceil`] (and similar for other signed integer types)
let impl_13__div_ceil (x y: i16)
    : Prims.Pure i16
      (requires y <>. mk_i16 0 && ~.((x =. impl_13__MIN <: bool) && (y =. mk_i16 (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let d:i16 = x /! y in
  let r:i16 = x %! y in
  if r >. mk_i16 0 && y >. mk_i16 0 || r <. mk_i16 0 && y <. mk_i16 0 then d +! mk_i16 1 else d

/// See [`std::primitive::i8::strict_neg`] (and similar for other integer types)
let impl_13__strict_neg (x: i16)
    : Prims.Pure i16 (requires x <>. impl_13__MIN) (fun _ -> Prims.l_True) =
  if x =. impl_13__MIN
  then Core_models.Panicking.Internal.panic #i16 ()
  else impl_13__wrapping_neg x

/// See [`std::primitive::i8::unchecked_neg`] (and similar for other signed integer types)
let impl_13__unchecked_neg (x: i16)
    : Prims.Pure i16 (requires x <>. impl_13__MIN) (fun _ -> Prims.l_True) = mk_i16 0 -! x

/// See [`std::primitive::i8::strict_abs`] (and similar for other signed integer types)
let impl_13__strict_abs (x: i16)
    : Prims.Pure i16 (requires x <>. impl_13__MIN) (fun _ -> Prims.l_True) =
  if x <. mk_i16 0 then impl_13__strict_neg x else x

/// See [`std::primitive::i8::strict_pow`] (and similar for other integer types)
let impl_13__strict_pow (x: i16) (exp: u32)
    : Prims.Pure i16
      (requires (impl_13__overflowing_pow x exp <: (i16 & bool))._2 =. false)
      (fun _ -> Prims.l_True) =
  let (result: i16), (overflowed: bool) = impl_13__overflowing_pow x exp in
  if overflowed then Core_models.Panicking.Internal.panic #i16 () else result

/// See [`std::primitive::i8::strict_add`] (and similar for other integer types)
let impl_13__strict_add (x y: i16)
    : Prims.Pure i16
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_13__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_13__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: i16), (overflowed: bool) = impl_13__overflowing_add x y in
  if overflowed then Core_models.Panicking.Internal.panic #i16 () else result

/// See [`std::primitive::i8::strict_sub`] (and similar for other integer types)
let impl_13__strict_sub (x y: i16)
    : Prims.Pure i16
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_13__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_13__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: i16), (overflowed: bool) = impl_13__overflowing_sub x y in
  if overflowed then Core_models.Panicking.Internal.panic #i16 () else result

/// See [`std::primitive::i8::strict_mul`] (and similar for other integer types)
let impl_13__strict_mul (x y: i16)
    : Prims.Pure i16
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_13__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_13__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: i16), (overflowed: bool) = impl_13__overflowing_mul x y in
  if overflowed then Core_models.Panicking.Internal.panic #i16 () else result

/// See [`std::primitive::i8::overflowing_div`] (and similar for other signed integer types)
let impl_13__overflowing_div (x y: i16)
    : Prims.Pure (i16 & bool) (requires y <>. mk_i16 0) (fun _ -> Prims.l_True) =
  if x =. impl_13__MIN && y =. mk_i16 (-1)
  then x, true <: (i16 & bool)
  else x /! y, false <: (i16 & bool)

/// See [`std::primitive::i8::overflowing_rem`] (and similar for other signed integer types)
let impl_13__overflowing_rem (x y: i16)
    : Prims.Pure (i16 & bool) (requires y <>. mk_i16 0) (fun _ -> Prims.l_True) =
  if y =. mk_i16 (-1)
  then mk_i16 0, x =. impl_13__MIN <: (i16 & bool)
  else x %! y, false <: (i16 & bool)

/// See [`std::primitive::i8::wrapping_div`] (and similar for other signed integer types)
let impl_13__wrapping_div (x y: i16)
    : Prims.Pure i16 (requires y <>. mk_i16 0) (fun _ -> Prims.l_True) =
  let (result: i16), (_: bool) = impl_13__overflowing_div x y in
  result

/// See [`std::primitive::i8::wrapping_rem`] (and similar for other signed integer types)
let impl_13__wrapping_rem (x y: i16)
    : Prims.Pure i16 (requires y <>. mk_i16 0) (fun _ -> Prims.l_True) =
  let (result: i16), (_: bool) = impl_13__overflowing_rem x y in
  result

/// See [`std::primitive::i8::saturating_div`] (and similar for other signed integer types)
let impl_13__saturating_div (x y: i16)
    : Prims.Pure i16 (requires y <>. mk_i16 0) (fun _ -> Prims.l_True) =
  let (result: i16), (overflowed: bool) = impl_13__overflowing_div x y in
  if overflowed then impl_13__MAX else result

/// See [`std::primitive::i8::strict_div`] (and similar for other signed integer types)
let impl_13__strict_div (x y: i16)
    : Prims.Pure i16
      (requires y <>. mk_i16 0 && ~.((x =. impl_13__MIN <: bool) && (y =. mk_i16 (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let (result: i16), (overflowed: bool) = impl_13__overflowing_div x y in
  if overflowed then Core_models.Panicking.Internal.panic #i16 () else result

/// See [`std::primitive::i8::strict_rem`] (and similar for other signed integer types)
let impl_13__strict_rem (x y: i16)
    : Prims.Pure i16
      (requires y <>. mk_i16 0 && ~.((x =. impl_13__MIN <: bool) && (y =. mk_i16 (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let (result: i16), (overflowed: bool) = impl_13__overflowing_rem x y in
  if overflowed then Core_models.Panicking.Internal.panic #i16 () else result

/// See [`std::primitive::i8::div_euclid`] (and similar for other signed integer types)
let impl_13__div_euclid (x y: i16)
    : Prims.Pure i16
      (requires y <>. mk_i16 0 && ~.((x =. impl_13__MIN <: bool) && (y =. mk_i16 (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let q:i16 = x /! y in
  if (x %! y <: i16) <. mk_i16 0
  then
    if y >. mk_i16 0 then impl_13__wrapping_sub q (mk_i16 1) else impl_13__wrapping_add q (mk_i16 1)
  else q

/// See [`std::primitive::i8::overflowing_div_euclid`] (and similar for other signed integer types)
let impl_13__overflowing_div_euclid (x y: i16)
    : Prims.Pure (i16 & bool) (requires y <>. mk_i16 0) (fun _ -> Prims.l_True) =
  if x =. impl_13__MIN && y =. mk_i16 (-1)
  then x, true <: (i16 & bool)
  else impl_13__div_euclid x y, false <: (i16 & bool)

/// See [`std::primitive::i8::wrapping_div_euclid`] (and similar for other signed integer types)
let impl_13__wrapping_div_euclid (x y: i16)
    : Prims.Pure i16 (requires y <>. mk_i16 0) (fun _ -> Prims.l_True) =
  let (result: i16), (_: bool) = impl_13__overflowing_div_euclid x y in
  result

/// See [`std::primitive::i8::strict_div_euclid`] (and similar for other signed integer types)
let impl_13__strict_div_euclid (x y: i16)
    : Prims.Pure i16
      (requires y <>. mk_i16 0 && ~.((x =. impl_13__MIN <: bool) && (y =. mk_i16 (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let (result: i16), (overflowed: bool) = impl_13__overflowing_div_euclid x y in
  if overflowed then Core_models.Panicking.Internal.panic #i16 () else result

/// See [`std::primitive::i8::overflowing_rem_euclid`] (and similar for other signed integer types)
let impl_13__overflowing_rem_euclid (x y: i16)
    : Prims.Pure (i16 & bool) (requires y <>. mk_i16 0) (fun _ -> Prims.l_True) =
  if y =. mk_i16 (-1)
  then mk_i16 0, x =. impl_13__MIN <: (i16 & bool)
  else impl_13__rem_euclid x y, false <: (i16 & bool)

/// See [`std::primitive::i8::wrapping_rem_euclid`] (and similar for other signed integer types)
let impl_13__wrapping_rem_euclid (x y: i16)
    : Prims.Pure i16 (requires y <>. mk_i16 0) (fun _ -> Prims.l_True) =
  let (result: i16), (_: bool) = impl_13__overflowing_rem_euclid x y in
  result

/// See [`std::primitive::i8::strict_rem_euclid`] (and similar for other signed integer types)
let impl_13__strict_rem_euclid (x y: i16)
    : Prims.Pure i16
      (requires y <>. mk_i16 0 && ~.((x =. impl_13__MIN <: bool) && (y =. mk_i16 (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let (result: i16), (overflowed: bool) = impl_13__overflowing_rem_euclid x y in
  if overflowed then Core_models.Panicking.Internal.panic #i16 () else result

/// See [`std::primitive::i8::div_floor`] (and similar for other signed integer types)
let impl_13__div_floor (x y: i16)
    : Prims.Pure i16
      (requires y <>. mk_i16 0 && ~.((x =. impl_13__MIN <: bool) && (y =. mk_i16 (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let d:i16 = x /! y in
  let r:i16 = x %! y in
  if r <>. mk_i16 0 && (x <. mk_i16 0 <: bool) <>. (y <. mk_i16 0 <: bool)
  then impl_13__wrapping_sub d (mk_i16 1)
  else d

/// See [`std::primitive::i8::unchecked_div_exact`] (and similar for other signed integer types)
let impl_13__unchecked_div_exact (x y: i16)
    : Prims.Pure i16 (requires y >. mk_i16 0 && (x %! y <: i16) =. mk_i16 0) (fun _ -> Prims.l_True) =
  x /! y

/// See [`std::primitive::i8::strict_add_unsigned`] (and similar for other signed integer types)
let impl_13__strict_add_unsigned (x: i16) (y: u16)
    : Prims.Pure i16
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_13__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: i16), (overflowed: bool) = impl_13__overflowing_add_unsigned x y in
  if overflowed then Core_models.Panicking.Internal.panic #i16 () else result

/// See [`std::primitive::i8::strict_sub_unsigned`] (and similar for other signed integer types)
let impl_13__strict_sub_unsigned (x: i16) (y: u16)
    : Prims.Pure i16
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_13__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: i16), (overflowed: bool) = impl_13__overflowing_sub_unsigned x y in
  if overflowed then Core_models.Panicking.Internal.panic #i16 () else result

/// See [`std::primitive::i8::strict_shl`] (and similar for other integer types)
let impl_13__strict_shl (x: i16) (n: u32)
    : Prims.Pure i16 (requires n <. impl_13__BITS) (fun _ -> Prims.l_True) =
  if n <. impl_13__BITS then x <<! n else Core_models.Panicking.Internal.panic #i16 ()

/// See [`std::primitive::i8::strict_shr`] (and similar for other integer types)
let impl_13__strict_shr (x: i16) (n: u32)
    : Prims.Pure i16 (requires n <. impl_13__BITS) (fun _ -> Prims.l_True) =
  if n <. impl_13__BITS then x >>! n else Core_models.Panicking.Internal.panic #i16 ()

/// See [`std::primitive::i8::unchecked_shl`] (and similar for other integer types)
let impl_13__unchecked_shl (x: i16) (n: u32)
    : Prims.Pure i16 (requires n <. impl_13__BITS) (fun _ -> Prims.l_True) = x <<! n

/// See [`std::primitive::i8::unchecked_shr`] (and similar for other integer types)
let impl_13__unchecked_shr (x: i16) (n: u32)
    : Prims.Pure i16 (requires n <. impl_13__BITS) (fun _ -> Prims.l_True) = x >>! n

/// See [`std::primitive::i8::unchecked_shl_exact`] (and similar for other signed integer types)
let impl_13__unchecked_shl_exact (x: i16) (n: u32)
    : Prims.Pure i16
      (requires
        (n <. (impl_13__leading_zeros x <: u32) || n <. (impl_13__leading_ones x <: u32)) &&
        n <. impl_13__BITS)
      (fun _ -> Prims.l_True) = x <<! n

/// See [`std::primitive::i8::unchecked_shr_exact`] (and similar for other integer types)
let impl_13__unchecked_shr_exact (x: i16) (n: u32)
    : Prims.Pure i16
      (requires n <=. (impl_13__trailing_zeros x <: u32) && n <. impl_13__BITS)
      (fun _ -> Prims.l_True) = x >>! n

/// See [`std::primitive::i8::MIN`] (and similar for other signed integer types)
let impl_14__MIN: i32 = mk_i32 (-2147483648)

/// See [`std::primitive::i8::MAX`] (and similar for other signed integer types)
let impl_14__MAX: i32 = mk_i32 2147483647

/// See [`std::primitive::i8::BITS`] (and similar for other signed integer types)
let impl_14__BITS: u32 = mk_u32 32

let impl_14__wrapping_add (x y: i32) : i32 = Rust_primitives.Arithmetic.wrapping_add_i32 x y

/// See [`std::primitive::u8::saturating_add`] (and similar for other integer types)
let impl_14__saturating_add (x y: i32) : i32 = Rust_primitives.Arithmetic.saturating_add_i32 x y

/// See [`std::primitive::u8::overflowing_add`] (and similar for other integer types)
let impl_14__overflowing_add (x y: i32) : (i32 & bool) =
  Rust_primitives.Arithmetic.overflowing_add_i32 x y

/// See [`std::primitive::u8::wrapping_sub`] (and similar for other integer types)
let impl_14__wrapping_sub (x y: i32) : i32 = Rust_primitives.Arithmetic.wrapping_sub_i32 x y

/// See [`std::primitive::u8::saturating_sub`] (and similar for other integer types)
let impl_14__saturating_sub (x y: i32) : i32 = Rust_primitives.Arithmetic.saturating_sub_i32 x y

/// See [`std::primitive::u8::overflowing_sub`] (and similar for other integer types)
let impl_14__overflowing_sub (x y: i32) : (i32 & bool) =
  Rust_primitives.Arithmetic.overflowing_sub_i32 x y

/// See [`std::primitive::u8::wrapping_mul`] (and similar for other integer types)
let impl_14__wrapping_mul (x y: i32) : i32 = Rust_primitives.Arithmetic.wrapping_mul_i32 x y

/// See [`std::primitive::u8::saturating_mul`] (and similar for other integer types)
let impl_14__saturating_mul (x y: i32) : i32 = Rust_primitives.Arithmetic.saturating_mul_i32 x y

/// See [`std::primitive::u8::overflowing_mul`] (and similar for other integer types)
let impl_14__overflowing_mul (x y: i32) : (i32 & bool) =
  Rust_primitives.Arithmetic.overflowing_mul_i32 x y

/// See [`std::primitive::u8::pow`] (and similar for other integer types)
let impl_14__pow (x: i32) (exp: u32) : i32 = Rust_primitives.Arithmetic.pow_i32 x exp

/// See [`std::primitive::u8::overflowing_pow`] (and similar for other integer types)
let impl_14__overflowing_pow (x: i32) (exp: u32) : (i32 & bool) =
  Rust_primitives.Arithmetic.overflowing_pow_i32 x exp

/// See [`std::primitive::u8::count_ones`] (and similar for other integer types)
let impl_14__count_ones (x: i32) : u32 = Rust_primitives.Arithmetic.count_ones_i32 x

/// See [`std::primitive::u8::rotate_right`] (and similar for other integer types)
assume
val impl_14__rotate_right': x: i32 -> n: u32 -> i32

unfold
let impl_14__rotate_right = impl_14__rotate_right'

/// See [`std::primitive::u8::rotate_left`] (and similar for other integer types)
assume
val impl_14__rotate_left': x: i32 -> n: u32 -> i32

unfold
let impl_14__rotate_left = impl_14__rotate_left'

/// See [`std::primitive::u8::leading_zeros`] (and similar for other integer types)
assume
val impl_14__leading_zeros': x: i32 -> u32

unfold
let impl_14__leading_zeros = impl_14__leading_zeros'

/// See [`std::primitive::u8::ilog2`] (and similar for other integer types)
assume
val impl_14__ilog2': x: i32 -> u32

unfold
let impl_14__ilog2 = impl_14__ilog2'

/// See [`std::primitive::u8::from_be_bytes`] (and similar for other integer types)
assume
val impl_14__from_be_bytes': bytes: t_Array u8 (mk_usize 4) -> i32

unfold
let impl_14__from_be_bytes = impl_14__from_be_bytes'

/// See [`std::primitive::u8::from_le_bytes`] (and similar for other integer types)
assume
val impl_14__from_le_bytes': bytes: t_Array u8 (mk_usize 4) -> i32

unfold
let impl_14__from_le_bytes = impl_14__from_le_bytes'

/// See [`std::primitive::u8::to_be_bytes`] (and similar for other integer types)
assume
val impl_14__to_be_bytes': bytes: i32 -> t_Array u8 (mk_usize 4)

unfold
let impl_14__to_be_bytes = impl_14__to_be_bytes'

/// See [`std::primitive::u8::to_le_bytes`] (and similar for other integer types)
assume
val impl_14__to_le_bytes': bytes: i32 -> t_Array u8 (mk_usize 4)

unfold
let impl_14__to_le_bytes = impl_14__to_le_bytes'

/// See [`std::primitive::i8::signum`] (and similar for other signed integer types)
let impl_14__signum (x: i32) : i32 =
  if x >. mk_i32 0 then mk_i32 1 else if x =. mk_i32 0 then mk_i32 0 else mk_i32 (-1)

/// See [`std::primitive::i8::wrapping_neg`] (and similar for other signed integer types)
let impl_14__wrapping_neg (x: i32) : i32 = Rust_primitives.Arithmetic.wrapping_sub_i32 (mk_i32 0) x

/// See [`std::primitive::i8::min_value`] (and similar for other integer types)
let impl_14__min_value (_: Prims.unit) : i32 = impl_14__MIN

/// See [`std::primitive::i8::max_value`] (and similar for other integer types)
let impl_14__max_value (_: Prims.unit) : i32 = impl_14__MAX

/// See [`std::primitive::i8::cast_unsigned`] (and similar for other signed integer types)
let impl_14__cast_unsigned (x: i32) : u32 = cast (x <: i32) <: u32

/// See [`std::primitive::i8::is_positive`] (and similar for other signed integer types)
let impl_14__is_positive (x: i32) : bool = x >. mk_i32 0

/// See [`std::primitive::i8::is_negative`] (and similar for other signed integer types)
let impl_14__is_negative (x: i32) : bool = x <. mk_i32 0

/// See [`std::primitive::i8::count_zeros`] (and similar for other integer types)
let impl_14__count_zeros (x: i32) : u32 = impl_14__BITS -! (impl_14__count_ones x <: u32)

/// See [`std::primitive::i8::overflowing_neg`] (and similar for other integer types)
let impl_14__overflowing_neg (x: i32) : (i32 & bool) =
  if x =. impl_14__MIN
  then impl_14__MIN, true <: (i32 & bool)
  else impl_14__wrapping_neg x, false <: (i32 & bool)

/// See [`std::primitive::i8::saturating_neg`] (and similar for other signed integer types)
let impl_14__saturating_neg (x: i32) : i32 =
  if x =. impl_14__MIN then impl_14__MAX else impl_14__wrapping_neg x

/// See [`std::primitive::i8::wrapping_abs`] (and similar for other signed integer types)
let impl_14__wrapping_abs (x: i32) : i32 = if x <. mk_i32 0 then impl_14__wrapping_neg x else x

/// See [`std::primitive::i8::overflowing_abs`] (and similar for other signed integer types)
let impl_14__overflowing_abs (x: i32) : (i32 & bool) =
  impl_14__wrapping_abs x, x =. impl_14__MIN <: (i32 & bool)

/// See [`std::primitive::i8::saturating_abs`] (and similar for other signed integer types)
let impl_14__saturating_abs (x: i32) : i32 = if x <. mk_i32 0 then impl_14__saturating_neg x else x

/// See [`std::primitive::i8::unsigned_abs`] (and similar for other signed integer types)
let impl_14__unsigned_abs (x: i32) : u32 = cast (impl_14__wrapping_abs x <: i32) <: u32

/// See [`std::primitive::i8::wrapping_pow`] (and similar for other integer types)
let impl_14__wrapping_pow (x: i32) (exp: u32) : i32 =
  let (result: i32), (_: bool) = impl_14__overflowing_pow x exp in
  result

/// See [`std::primitive::i8::saturating_pow`] (and similar for other signed integer types)
let impl_14__saturating_pow (x: i32) (exp: u32) : i32 =
  let (result: i32), (overflowed: bool) = impl_14__overflowing_pow x exp in
  if ~.overflowed
  then result
  else if x <. mk_i32 0 && (exp %! mk_u32 2 <: u32) =. mk_u32 1 then impl_14__MIN else impl_14__MAX

/// See [`std::primitive::i8::abs_diff`] (and similar for other signed integer types)
let impl_14__abs_diff (x y: i32) : u32 =
  if x <. y
  then cast (impl_14__wrapping_sub y x <: i32) <: u32
  else cast (impl_14__wrapping_sub x y <: i32) <: u32

/// See [`std::primitive::i8::midpoint`] (and similar for other signed integer types)
let impl_14__midpoint (x y: i32) : i32 =
  let d:i32 = x ^. y in
  let t:i32 = impl_14__wrapping_add (d >>! mk_i32 1 <: i32) (x &. y <: i32) in
  if t <. mk_i32 0 then impl_14__wrapping_add t (d &. mk_i32 1 <: i32) else t

/// See [`std::primitive::i8::wrapping_add_unsigned`] (and similar for other signed integer types)
let impl_14__wrapping_add_unsigned (x: i32) (y: u32) : i32 =
  impl_14__wrapping_add x (cast (y <: u32) <: i32)

/// See [`std::primitive::i8::wrapping_sub_unsigned`] (and similar for other signed integer types)
let impl_14__wrapping_sub_unsigned (x: i32) (y: u32) : i32 =
  impl_14__wrapping_sub x (cast (y <: u32) <: i32)

/// See [`std::primitive::i8::overflowing_add_unsigned`] (and similar for other signed integer types)
let impl_14__overflowing_add_unsigned (x: i32) (y: u32) : (i32 & bool) =
  let rhs:i32 = cast (y <: u32) <: i32 in
  let (result: i32), (overflowed: bool) = impl_14__overflowing_add x rhs in
  result, overflowed <>. (rhs <. mk_i32 0 <: bool) <: (i32 & bool)

/// See [`std::primitive::i8::overflowing_sub_unsigned`] (and similar for other signed integer types)
let impl_14__overflowing_sub_unsigned (x: i32) (y: u32) : (i32 & bool) =
  let rhs:i32 = cast (y <: u32) <: i32 in
  let (result: i32), (overflowed: bool) = impl_14__overflowing_sub x rhs in
  result, overflowed <>. (rhs <. mk_i32 0 <: bool) <: (i32 & bool)

/// See [`std::primitive::i8::saturating_add_unsigned`] (and similar for other signed integer types)
let impl_14__saturating_add_unsigned (x: i32) (y: u32) : i32 =
  let (result: i32), (overflowed: bool) = impl_14__overflowing_add_unsigned x y in
  if overflowed then impl_14__MAX else result

/// See [`std::primitive::i8::saturating_sub_unsigned`] (and similar for other signed integer types)
let impl_14__saturating_sub_unsigned (x: i32) (y: u32) : i32 =
  let (result: i32), (overflowed: bool) = impl_14__overflowing_sub_unsigned x y in
  if overflowed then impl_14__MIN else result

/// See [`std::primitive::i8::reverse_bits`] (and similar for other signed integer types)
let impl_14__reverse_bits (x: i32) : i32 =
  cast (impl_8__reverse_bits (cast (x <: i32) <: u32) <: u32) <: i32

/// See [`std::primitive::i8::widening_mul`] (and similar for other signed integer types)
let impl_14__widening_mul (x y: i32) : (u32 & i32) =
  let (low: u32), (high: u32) =
    impl_8__widening_mul (cast (x <: i32) <: u32) (cast (y <: i32) <: u32)
  in
  let high:i32 = cast (high <: u32) <: i32 in
  let high:i32 = if x <. mk_i32 0 then impl_14__wrapping_sub high y else high in
  let high:i32 = if y <. mk_i32 0 then impl_14__wrapping_sub high x else high in
  low, high <: (u32 & i32)

/// See [`std::primitive::i8::carrying_mul_add`] (and similar for other signed integer types)
let impl_14__carrying_mul_add (x y carry add: i32) : (u32 & i32) =
  let (low: u32), (high: i32) = impl_14__widening_mul x y in
  let (low: u32), (c1: bool) = impl_8__overflowing_add low (cast (carry <: i32) <: u32) in
  let (low: u32), (c2: bool) = impl_8__overflowing_add low (cast (add <: i32) <: u32) in
  let high:i32 = impl_14__wrapping_add high (if c1 then mk_i32 1 else mk_i32 0) in
  let high:i32 = impl_14__wrapping_add high (if c2 then mk_i32 1 else mk_i32 0) in
  let high:i32 =
    impl_14__wrapping_add high (if carry <. mk_i32 0 <: bool then mk_i32 (-1) else mk_i32 0)
  in
  let high:i32 =
    impl_14__wrapping_add high (if add <. mk_i32 0 <: bool then mk_i32 (-1) else mk_i32 0)
  in
  low, high <: (u32 & i32)

/// See [`std::primitive::i8::carrying_mul`] (and similar for other signed integer types)
let impl_14__carrying_mul (x y carry: i32) : (u32 & i32) =
  impl_14__carrying_mul_add x y carry (mk_i32 0)

/// See [`std::primitive::i8::carrying_add`] (and similar for other integer types)
let impl_14__carrying_add (x y: i32) (carry: bool) : (i32 & bool) =
  let (a: i32), (b: bool) = impl_14__overflowing_add x y in
  let (c: i32), (d: bool) = impl_14__overflowing_add a (if carry then mk_i32 1 else mk_i32 0) in
  c, b <>. d <: (i32 & bool)

/// See [`std::primitive::i8::borrowing_sub`] (and similar for other integer types)
let impl_14__borrowing_sub (x y: i32) (borrow: bool) : (i32 & bool) =
  let (a: i32), (b: bool) = impl_14__overflowing_sub x y in
  let (c: i32), (d: bool) = impl_14__overflowing_sub a (if borrow then mk_i32 1 else mk_i32 0) in
  c, b <>. d <: (i32 & bool)

/// See [`std::primitive::i8::trailing_zeros`] (and similar for other integer types)
let impl_14__trailing_zeros (x: i32) : u32 =
  if x =. mk_i32 0
  then impl_14__BITS
  else
    impl_14__count_ones (impl_14__wrapping_sub (x &. (impl_14__wrapping_neg x <: i32) <: i32)
          (mk_i32 1)
        <:
        i32)

/// See [`std::primitive::i8::trailing_ones`] (and similar for other integer types)
let impl_14__trailing_ones (x: i32) : u32 =
  impl_14__trailing_zeros (impl_14__wrapping_sub (mk_i32 (-1)) x <: i32)

/// See [`std::primitive::i8::leading_ones`] (and similar for other integer types)
let impl_14__leading_ones (x: i32) : u32 =
  impl_14__leading_zeros (impl_14__wrapping_sub (mk_i32 (-1)) x <: i32)

/// See [`std::primitive::i8::isolate_lowest_one`] (and similar for other integer types)
let impl_14__isolate_lowest_one (x: i32) : i32 = x &. (impl_14__wrapping_neg x <: i32)

/// See [`std::primitive::i8::swap_bytes`] (and similar for other integer types)
let impl_14__swap_bytes (x: i32) : i32 =
  impl_14__from_le_bytes (impl_14__to_be_bytes x <: t_Array u8 (mk_usize 4))

/// See [`std::primitive::i8::to_be`] (and similar for other integer types)
let impl_14__to_be (x: i32) : i32 = impl_14__swap_bytes x

/// See [`std::primitive::i8::to_le`] (and similar for other integer types)
let impl_14__to_le (x: i32) : i32 = x

/// See [`std::primitive::i8::from_be`] (and similar for other integer types)
let impl_14__from_be (x: i32) : i32 = impl_14__swap_bytes x

/// See [`std::primitive::i8::from_le`] (and similar for other integer types)
let impl_14__from_le (x: i32) : i32 = x

/// See [`std::primitive::i8::to_ne_bytes`] (and similar for other integer types)
let impl_14__to_ne_bytes (x: i32) : t_Array u8 (mk_usize 4) = impl_14__to_le_bytes x

/// See [`std::primitive::i8::from_ne_bytes`] (and similar for other integer types)
let impl_14__from_ne_bytes (bytes: t_Array u8 (mk_usize 4)) : i32 = impl_14__from_le_bytes bytes

/// See [`std::primitive::i8::wrapping_shl`] (and similar for other integer types)
let impl_14__wrapping_shl (x: i32) (n: u32) : i32 = x <<! (n %! impl_14__BITS <: u32)

/// See [`std::primitive::i8::wrapping_shr`] (and similar for other integer types)
let impl_14__wrapping_shr (x: i32) (n: u32) : i32 = x >>! (n %! impl_14__BITS <: u32)

/// See [`std::primitive::i8::isolate_highest_one`] (and similar for other integer types)
let impl_14__isolate_highest_one (x: i32) : i32 =
  x &. (impl_14__wrapping_shr impl_14__MIN (impl_14__leading_zeros x <: u32) <: i32)

/// See [`std::primitive::i8::overflowing_shl`] (and similar for other integer types)
let impl_14__overflowing_shl (x: i32) (n: u32) : (i32 & bool) =
  impl_14__wrapping_shl x n, n >=. impl_14__BITS <: (i32 & bool)

/// See [`std::primitive::i8::overflowing_shr`] (and similar for other integer types)
let impl_14__overflowing_shr (x: i32) (n: u32) : (i32 & bool) =
  impl_14__wrapping_shr x n, n >=. impl_14__BITS <: (i32 & bool)

/// See [`std::primitive::i8::unbounded_shl`] (and similar for other integer types)
let impl_14__unbounded_shl (x: i32) (n: u32) : i32 =
  if n <. impl_14__BITS then x <<! n else mk_i32 0

/// See [`std::primitive::i8::unbounded_shr`] (and similar for other signed integer types)
let impl_14__unbounded_shr (x: i32) (n: u32) : i32 =
  if n <. impl_14__BITS then x >>! n else x >>! (impl_14__BITS -! mk_u32 1 <: u32)

/// See [`std::primitive::i8::clamp_magnitude`] (and similar for other signed integer types)
let impl_14__clamp_magnitude (x: i32) (limit: u32) : i32 =
  if limit >. (cast (impl_14__MAX <: i32) <: u32)
  then x
  else
    let hi:i32 = cast (limit <: u32) <: i32 in
    let lo:i32 = impl_14__wrapping_neg hi in
    if x <. lo then lo else if x >. hi then hi else x

/// See [`std::primitive::u8::unchecked_add`] (and similar for other integer types)
let impl_14__unchecked_add (x y: i32)
    : Prims.Pure i32
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_14__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_14__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) = x +! y

/// See [`std::primitive::u8::unchecked_sub`] (and similar for other integer types)
let impl_14__unchecked_sub (x y: i32)
    : Prims.Pure i32
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_14__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_14__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) = x -! y

/// See [`std::primitive::u8::unchecked_mul`] (and similar for other integer types)
let impl_14__unchecked_mul (x y: i32)
    : Prims.Pure i32
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_14__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_14__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) = x *! y

/// See [`std::primitive::u8::rem_euclid`] (and similar for other integer types)
let impl_14__rem_euclid (x y: i32)
    : Prims.Pure i32
      (requires y <>. mk_i32 0 && ~.((x =. impl_14__MIN <: bool) && (y =. mk_i32 (-1) <: bool)))
      (fun _ -> Prims.l_True) = Rust_primitives.Arithmetic.rem_euclid_i32 x y

/// See [`std::primitive::i8::abs`] (and similar for other signed integer types)
let impl_14__abs (x: i32) : Prims.Pure i32 (requires x >. impl_14__MIN) (fun _ -> Prims.l_True) =
  Rust_primitives.Arithmetic.abs_i32 x

/// See [`std::primitive::u8::unchecked_div`] (and similar for other integer types)
let impl_14__unchecked_div (x y: i32)
    : Prims.Pure i32
      (requires y <>. mk_i32 0 && (x <>. impl_14__MIN || y <>. mk_i32 (-1)))
      (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::unchecked_rem`] (and similar for other integer types)
let impl_14__unchecked_rem (x y: i32)
    : Prims.Pure i32
      (requires y <>. mk_i32 0 && (x <>. impl_14__MIN || y <>. mk_i32 (-1)))
      (fun _ -> Prims.l_True) = x %! y

/// See [`std::primitive::i8::div_ceil`] (and similar for other signed integer types)
let impl_14__div_ceil (x y: i32)
    : Prims.Pure i32
      (requires y <>. mk_i32 0 && ~.((x =. impl_14__MIN <: bool) && (y =. mk_i32 (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let d:i32 = x /! y in
  let r:i32 = x %! y in
  if r >. mk_i32 0 && y >. mk_i32 0 || r <. mk_i32 0 && y <. mk_i32 0 then d +! mk_i32 1 else d

/// See [`std::primitive::i8::strict_neg`] (and similar for other integer types)
let impl_14__strict_neg (x: i32)
    : Prims.Pure i32 (requires x <>. impl_14__MIN) (fun _ -> Prims.l_True) =
  if x =. impl_14__MIN
  then Core_models.Panicking.Internal.panic #i32 ()
  else impl_14__wrapping_neg x

/// See [`std::primitive::i8::unchecked_neg`] (and similar for other signed integer types)
let impl_14__unchecked_neg (x: i32)
    : Prims.Pure i32 (requires x <>. impl_14__MIN) (fun _ -> Prims.l_True) = mk_i32 0 -! x

/// See [`std::primitive::i8::strict_abs`] (and similar for other signed integer types)
let impl_14__strict_abs (x: i32)
    : Prims.Pure i32 (requires x <>. impl_14__MIN) (fun _ -> Prims.l_True) =
  if x <. mk_i32 0 then impl_14__strict_neg x else x

/// See [`std::primitive::i8::strict_pow`] (and similar for other integer types)
let impl_14__strict_pow (x: i32) (exp: u32)
    : Prims.Pure i32
      (requires (impl_14__overflowing_pow x exp <: (i32 & bool))._2 =. false)
      (fun _ -> Prims.l_True) =
  let (result: i32), (overflowed: bool) = impl_14__overflowing_pow x exp in
  if overflowed then Core_models.Panicking.Internal.panic #i32 () else result

/// See [`std::primitive::i8::strict_add`] (and similar for other integer types)
let impl_14__strict_add (x y: i32)
    : Prims.Pure i32
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_14__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_14__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: i32), (overflowed: bool) = impl_14__overflowing_add x y in
  if overflowed then Core_models.Panicking.Internal.panic #i32 () else result

/// See [`std::primitive::i8::strict_sub`] (and similar for other integer types)
let impl_14__strict_sub (x y: i32)
    : Prims.Pure i32
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_14__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_14__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: i32), (overflowed: bool) = impl_14__overflowing_sub x y in
  if overflowed then Core_models.Panicking.Internal.panic #i32 () else result

/// See [`std::primitive::i8::strict_mul`] (and similar for other integer types)
let impl_14__strict_mul (x y: i32)
    : Prims.Pure i32
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_14__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_14__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: i32), (overflowed: bool) = impl_14__overflowing_mul x y in
  if overflowed then Core_models.Panicking.Internal.panic #i32 () else result

/// See [`std::primitive::i8::overflowing_div`] (and similar for other signed integer types)
let impl_14__overflowing_div (x y: i32)
    : Prims.Pure (i32 & bool) (requires y <>. mk_i32 0) (fun _ -> Prims.l_True) =
  if x =. impl_14__MIN && y =. mk_i32 (-1)
  then x, true <: (i32 & bool)
  else x /! y, false <: (i32 & bool)

/// See [`std::primitive::i8::overflowing_rem`] (and similar for other signed integer types)
let impl_14__overflowing_rem (x y: i32)
    : Prims.Pure (i32 & bool) (requires y <>. mk_i32 0) (fun _ -> Prims.l_True) =
  if y =. mk_i32 (-1)
  then mk_i32 0, x =. impl_14__MIN <: (i32 & bool)
  else x %! y, false <: (i32 & bool)

/// See [`std::primitive::i8::wrapping_div`] (and similar for other signed integer types)
let impl_14__wrapping_div (x y: i32)
    : Prims.Pure i32 (requires y <>. mk_i32 0) (fun _ -> Prims.l_True) =
  let (result: i32), (_: bool) = impl_14__overflowing_div x y in
  result

/// See [`std::primitive::i8::wrapping_rem`] (and similar for other signed integer types)
let impl_14__wrapping_rem (x y: i32)
    : Prims.Pure i32 (requires y <>. mk_i32 0) (fun _ -> Prims.l_True) =
  let (result: i32), (_: bool) = impl_14__overflowing_rem x y in
  result

/// See [`std::primitive::i8::saturating_div`] (and similar for other signed integer types)
let impl_14__saturating_div (x y: i32)
    : Prims.Pure i32 (requires y <>. mk_i32 0) (fun _ -> Prims.l_True) =
  let (result: i32), (overflowed: bool) = impl_14__overflowing_div x y in
  if overflowed then impl_14__MAX else result

/// See [`std::primitive::i8::strict_div`] (and similar for other signed integer types)
let impl_14__strict_div (x y: i32)
    : Prims.Pure i32
      (requires y <>. mk_i32 0 && ~.((x =. impl_14__MIN <: bool) && (y =. mk_i32 (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let (result: i32), (overflowed: bool) = impl_14__overflowing_div x y in
  if overflowed then Core_models.Panicking.Internal.panic #i32 () else result

/// See [`std::primitive::i8::strict_rem`] (and similar for other signed integer types)
let impl_14__strict_rem (x y: i32)
    : Prims.Pure i32
      (requires y <>. mk_i32 0 && ~.((x =. impl_14__MIN <: bool) && (y =. mk_i32 (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let (result: i32), (overflowed: bool) = impl_14__overflowing_rem x y in
  if overflowed then Core_models.Panicking.Internal.panic #i32 () else result

/// See [`std::primitive::i8::div_euclid`] (and similar for other signed integer types)
let impl_14__div_euclid (x y: i32)
    : Prims.Pure i32
      (requires y <>. mk_i32 0 && ~.((x =. impl_14__MIN <: bool) && (y =. mk_i32 (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let q:i32 = x /! y in
  if (x %! y <: i32) <. mk_i32 0
  then
    if y >. mk_i32 0 then impl_14__wrapping_sub q (mk_i32 1) else impl_14__wrapping_add q (mk_i32 1)
  else q

/// See [`std::primitive::i8::overflowing_div_euclid`] (and similar for other signed integer types)
let impl_14__overflowing_div_euclid (x y: i32)
    : Prims.Pure (i32 & bool) (requires y <>. mk_i32 0) (fun _ -> Prims.l_True) =
  if x =. impl_14__MIN && y =. mk_i32 (-1)
  then x, true <: (i32 & bool)
  else impl_14__div_euclid x y, false <: (i32 & bool)

/// See [`std::primitive::i8::wrapping_div_euclid`] (and similar for other signed integer types)
let impl_14__wrapping_div_euclid (x y: i32)
    : Prims.Pure i32 (requires y <>. mk_i32 0) (fun _ -> Prims.l_True) =
  let (result: i32), (_: bool) = impl_14__overflowing_div_euclid x y in
  result

/// See [`std::primitive::i8::strict_div_euclid`] (and similar for other signed integer types)
let impl_14__strict_div_euclid (x y: i32)
    : Prims.Pure i32
      (requires y <>. mk_i32 0 && ~.((x =. impl_14__MIN <: bool) && (y =. mk_i32 (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let (result: i32), (overflowed: bool) = impl_14__overflowing_div_euclid x y in
  if overflowed then Core_models.Panicking.Internal.panic #i32 () else result

/// See [`std::primitive::i8::overflowing_rem_euclid`] (and similar for other signed integer types)
let impl_14__overflowing_rem_euclid (x y: i32)
    : Prims.Pure (i32 & bool) (requires y <>. mk_i32 0) (fun _ -> Prims.l_True) =
  if y =. mk_i32 (-1)
  then mk_i32 0, x =. impl_14__MIN <: (i32 & bool)
  else impl_14__rem_euclid x y, false <: (i32 & bool)

/// See [`std::primitive::i8::wrapping_rem_euclid`] (and similar for other signed integer types)
let impl_14__wrapping_rem_euclid (x y: i32)
    : Prims.Pure i32 (requires y <>. mk_i32 0) (fun _ -> Prims.l_True) =
  let (result: i32), (_: bool) = impl_14__overflowing_rem_euclid x y in
  result

/// See [`std::primitive::i8::strict_rem_euclid`] (and similar for other signed integer types)
let impl_14__strict_rem_euclid (x y: i32)
    : Prims.Pure i32
      (requires y <>. mk_i32 0 && ~.((x =. impl_14__MIN <: bool) && (y =. mk_i32 (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let (result: i32), (overflowed: bool) = impl_14__overflowing_rem_euclid x y in
  if overflowed then Core_models.Panicking.Internal.panic #i32 () else result

/// See [`std::primitive::i8::div_floor`] (and similar for other signed integer types)
let impl_14__div_floor (x y: i32)
    : Prims.Pure i32
      (requires y <>. mk_i32 0 && ~.((x =. impl_14__MIN <: bool) && (y =. mk_i32 (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let d:i32 = x /! y in
  let r:i32 = x %! y in
  if r <>. mk_i32 0 && (x <. mk_i32 0 <: bool) <>. (y <. mk_i32 0 <: bool)
  then impl_14__wrapping_sub d (mk_i32 1)
  else d

/// See [`std::primitive::i8::unchecked_div_exact`] (and similar for other signed integer types)
let impl_14__unchecked_div_exact (x y: i32)
    : Prims.Pure i32 (requires y >. mk_i32 0 && (x %! y <: i32) =. mk_i32 0) (fun _ -> Prims.l_True) =
  x /! y

/// See [`std::primitive::i8::strict_add_unsigned`] (and similar for other signed integer types)
let impl_14__strict_add_unsigned (x: i32) (y: u32)
    : Prims.Pure i32
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_14__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: i32), (overflowed: bool) = impl_14__overflowing_add_unsigned x y in
  if overflowed then Core_models.Panicking.Internal.panic #i32 () else result

/// See [`std::primitive::i8::strict_sub_unsigned`] (and similar for other signed integer types)
let impl_14__strict_sub_unsigned (x: i32) (y: u32)
    : Prims.Pure i32
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_14__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: i32), (overflowed: bool) = impl_14__overflowing_sub_unsigned x y in
  if overflowed then Core_models.Panicking.Internal.panic #i32 () else result

/// See [`std::primitive::i8::strict_shl`] (and similar for other integer types)
let impl_14__strict_shl (x: i32) (n: u32)
    : Prims.Pure i32 (requires n <. impl_14__BITS) (fun _ -> Prims.l_True) =
  if n <. impl_14__BITS then x <<! n else Core_models.Panicking.Internal.panic #i32 ()

/// See [`std::primitive::i8::strict_shr`] (and similar for other integer types)
let impl_14__strict_shr (x: i32) (n: u32)
    : Prims.Pure i32 (requires n <. impl_14__BITS) (fun _ -> Prims.l_True) =
  if n <. impl_14__BITS then x >>! n else Core_models.Panicking.Internal.panic #i32 ()

/// See [`std::primitive::i8::unchecked_shl`] (and similar for other integer types)
let impl_14__unchecked_shl (x: i32) (n: u32)
    : Prims.Pure i32 (requires n <. impl_14__BITS) (fun _ -> Prims.l_True) = x <<! n

/// See [`std::primitive::i8::unchecked_shr`] (and similar for other integer types)
let impl_14__unchecked_shr (x: i32) (n: u32)
    : Prims.Pure i32 (requires n <. impl_14__BITS) (fun _ -> Prims.l_True) = x >>! n

/// See [`std::primitive::i8::unchecked_shl_exact`] (and similar for other signed integer types)
let impl_14__unchecked_shl_exact (x: i32) (n: u32)
    : Prims.Pure i32
      (requires
        (n <. (impl_14__leading_zeros x <: u32) || n <. (impl_14__leading_ones x <: u32)) &&
        n <. impl_14__BITS)
      (fun _ -> Prims.l_True) = x <<! n

/// See [`std::primitive::i8::unchecked_shr_exact`] (and similar for other integer types)
let impl_14__unchecked_shr_exact (x: i32) (n: u32)
    : Prims.Pure i32
      (requires n <=. (impl_14__trailing_zeros x <: u32) && n <. impl_14__BITS)
      (fun _ -> Prims.l_True) = x >>! n

/// See [`std::primitive::i8::MIN`] (and similar for other signed integer types)
let impl_15__MIN: i64 = mk_i64 (-9223372036854775808)

/// See [`std::primitive::i8::MAX`] (and similar for other signed integer types)
let impl_15__MAX: i64 = mk_i64 9223372036854775807

/// See [`std::primitive::i8::BITS`] (and similar for other signed integer types)
let impl_15__BITS: u32 = mk_u32 64

let impl_15__wrapping_add (x y: i64) : i64 = Rust_primitives.Arithmetic.wrapping_add_i64 x y

/// See [`std::primitive::u8::saturating_add`] (and similar for other integer types)
let impl_15__saturating_add (x y: i64) : i64 = Rust_primitives.Arithmetic.saturating_add_i64 x y

/// See [`std::primitive::u8::overflowing_add`] (and similar for other integer types)
let impl_15__overflowing_add (x y: i64) : (i64 & bool) =
  Rust_primitives.Arithmetic.overflowing_add_i64 x y

/// See [`std::primitive::u8::wrapping_sub`] (and similar for other integer types)
let impl_15__wrapping_sub (x y: i64) : i64 = Rust_primitives.Arithmetic.wrapping_sub_i64 x y

/// See [`std::primitive::u8::saturating_sub`] (and similar for other integer types)
let impl_15__saturating_sub (x y: i64) : i64 = Rust_primitives.Arithmetic.saturating_sub_i64 x y

/// See [`std::primitive::u8::overflowing_sub`] (and similar for other integer types)
let impl_15__overflowing_sub (x y: i64) : (i64 & bool) =
  Rust_primitives.Arithmetic.overflowing_sub_i64 x y

/// See [`std::primitive::u8::wrapping_mul`] (and similar for other integer types)
let impl_15__wrapping_mul (x y: i64) : i64 = Rust_primitives.Arithmetic.wrapping_mul_i64 x y

/// See [`std::primitive::u8::saturating_mul`] (and similar for other integer types)
let impl_15__saturating_mul (x y: i64) : i64 = Rust_primitives.Arithmetic.saturating_mul_i64 x y

/// See [`std::primitive::u8::overflowing_mul`] (and similar for other integer types)
let impl_15__overflowing_mul (x y: i64) : (i64 & bool) =
  Rust_primitives.Arithmetic.overflowing_mul_i64 x y

/// See [`std::primitive::u8::pow`] (and similar for other integer types)
let impl_15__pow (x: i64) (exp: u32) : i64 = Rust_primitives.Arithmetic.pow_i64 x exp

/// See [`std::primitive::u8::overflowing_pow`] (and similar for other integer types)
let impl_15__overflowing_pow (x: i64) (exp: u32) : (i64 & bool) =
  Rust_primitives.Arithmetic.overflowing_pow_i64 x exp

/// See [`std::primitive::u8::count_ones`] (and similar for other integer types)
let impl_15__count_ones (x: i64) : u32 = Rust_primitives.Arithmetic.count_ones_i64 x

/// See [`std::primitive::u8::rotate_right`] (and similar for other integer types)
assume
val impl_15__rotate_right': x: i64 -> n: u32 -> i64

unfold
let impl_15__rotate_right = impl_15__rotate_right'

/// See [`std::primitive::u8::rotate_left`] (and similar for other integer types)
assume
val impl_15__rotate_left': x: i64 -> n: u32 -> i64

unfold
let impl_15__rotate_left = impl_15__rotate_left'

/// See [`std::primitive::u8::leading_zeros`] (and similar for other integer types)
assume
val impl_15__leading_zeros': x: i64 -> u32

unfold
let impl_15__leading_zeros = impl_15__leading_zeros'

/// See [`std::primitive::u8::ilog2`] (and similar for other integer types)
assume
val impl_15__ilog2': x: i64 -> u32

unfold
let impl_15__ilog2 = impl_15__ilog2'

/// See [`std::primitive::u8::from_be_bytes`] (and similar for other integer types)
assume
val impl_15__from_be_bytes': bytes: t_Array u8 (mk_usize 8) -> i64

unfold
let impl_15__from_be_bytes = impl_15__from_be_bytes'

/// See [`std::primitive::u8::from_le_bytes`] (and similar for other integer types)
assume
val impl_15__from_le_bytes': bytes: t_Array u8 (mk_usize 8) -> i64

unfold
let impl_15__from_le_bytes = impl_15__from_le_bytes'

/// See [`std::primitive::u8::to_be_bytes`] (and similar for other integer types)
assume
val impl_15__to_be_bytes': bytes: i64 -> t_Array u8 (mk_usize 8)

unfold
let impl_15__to_be_bytes = impl_15__to_be_bytes'

/// See [`std::primitive::u8::to_le_bytes`] (and similar for other integer types)
assume
val impl_15__to_le_bytes': bytes: i64 -> t_Array u8 (mk_usize 8)

unfold
let impl_15__to_le_bytes = impl_15__to_le_bytes'

/// See [`std::primitive::i8::signum`] (and similar for other signed integer types)
let impl_15__signum (x: i64) : i64 =
  if x >. mk_i64 0 then mk_i64 1 else if x =. mk_i64 0 then mk_i64 0 else mk_i64 (-1)

/// See [`std::primitive::i8::wrapping_neg`] (and similar for other signed integer types)
let impl_15__wrapping_neg (x: i64) : i64 = Rust_primitives.Arithmetic.wrapping_sub_i64 (mk_i64 0) x

/// See [`std::primitive::i8::min_value`] (and similar for other integer types)
let impl_15__min_value (_: Prims.unit) : i64 = impl_15__MIN

/// See [`std::primitive::i8::max_value`] (and similar for other integer types)
let impl_15__max_value (_: Prims.unit) : i64 = impl_15__MAX

/// See [`std::primitive::i8::cast_unsigned`] (and similar for other signed integer types)
let impl_15__cast_unsigned (x: i64) : u64 = cast (x <: i64) <: u64

/// See [`std::primitive::i8::is_positive`] (and similar for other signed integer types)
let impl_15__is_positive (x: i64) : bool = x >. mk_i64 0

/// See [`std::primitive::i8::is_negative`] (and similar for other signed integer types)
let impl_15__is_negative (x: i64) : bool = x <. mk_i64 0

/// See [`std::primitive::i8::count_zeros`] (and similar for other integer types)
let impl_15__count_zeros (x: i64) : u32 = impl_15__BITS -! (impl_15__count_ones x <: u32)

/// See [`std::primitive::i8::overflowing_neg`] (and similar for other integer types)
let impl_15__overflowing_neg (x: i64) : (i64 & bool) =
  if x =. impl_15__MIN
  then impl_15__MIN, true <: (i64 & bool)
  else impl_15__wrapping_neg x, false <: (i64 & bool)

/// See [`std::primitive::i8::saturating_neg`] (and similar for other signed integer types)
let impl_15__saturating_neg (x: i64) : i64 =
  if x =. impl_15__MIN then impl_15__MAX else impl_15__wrapping_neg x

/// See [`std::primitive::i8::wrapping_abs`] (and similar for other signed integer types)
let impl_15__wrapping_abs (x: i64) : i64 = if x <. mk_i64 0 then impl_15__wrapping_neg x else x

/// See [`std::primitive::i8::overflowing_abs`] (and similar for other signed integer types)
let impl_15__overflowing_abs (x: i64) : (i64 & bool) =
  impl_15__wrapping_abs x, x =. impl_15__MIN <: (i64 & bool)

/// See [`std::primitive::i8::saturating_abs`] (and similar for other signed integer types)
let impl_15__saturating_abs (x: i64) : i64 = if x <. mk_i64 0 then impl_15__saturating_neg x else x

/// See [`std::primitive::i8::unsigned_abs`] (and similar for other signed integer types)
let impl_15__unsigned_abs (x: i64) : u64 = cast (impl_15__wrapping_abs x <: i64) <: u64

/// See [`std::primitive::i8::wrapping_pow`] (and similar for other integer types)
let impl_15__wrapping_pow (x: i64) (exp: u32) : i64 =
  let (result: i64), (_: bool) = impl_15__overflowing_pow x exp in
  result

/// See [`std::primitive::i8::saturating_pow`] (and similar for other signed integer types)
let impl_15__saturating_pow (x: i64) (exp: u32) : i64 =
  let (result: i64), (overflowed: bool) = impl_15__overflowing_pow x exp in
  if ~.overflowed
  then result
  else if x <. mk_i64 0 && (exp %! mk_u32 2 <: u32) =. mk_u32 1 then impl_15__MIN else impl_15__MAX

/// See [`std::primitive::i8::abs_diff`] (and similar for other signed integer types)
let impl_15__abs_diff (x y: i64) : u64 =
  if x <. y
  then cast (impl_15__wrapping_sub y x <: i64) <: u64
  else cast (impl_15__wrapping_sub x y <: i64) <: u64

/// See [`std::primitive::i8::midpoint`] (and similar for other signed integer types)
let impl_15__midpoint (x y: i64) : i64 =
  let d:i64 = x ^. y in
  let t:i64 = impl_15__wrapping_add (d >>! mk_i32 1 <: i64) (x &. y <: i64) in
  if t <. mk_i64 0 then impl_15__wrapping_add t (d &. mk_i64 1 <: i64) else t

/// See [`std::primitive::i8::wrapping_add_unsigned`] (and similar for other signed integer types)
let impl_15__wrapping_add_unsigned (x: i64) (y: u64) : i64 =
  impl_15__wrapping_add x (cast (y <: u64) <: i64)

/// See [`std::primitive::i8::wrapping_sub_unsigned`] (and similar for other signed integer types)
let impl_15__wrapping_sub_unsigned (x: i64) (y: u64) : i64 =
  impl_15__wrapping_sub x (cast (y <: u64) <: i64)

/// See [`std::primitive::i8::overflowing_add_unsigned`] (and similar for other signed integer types)
let impl_15__overflowing_add_unsigned (x: i64) (y: u64) : (i64 & bool) =
  let rhs:i64 = cast (y <: u64) <: i64 in
  let (result: i64), (overflowed: bool) = impl_15__overflowing_add x rhs in
  result, overflowed <>. (rhs <. mk_i64 0 <: bool) <: (i64 & bool)

/// See [`std::primitive::i8::overflowing_sub_unsigned`] (and similar for other signed integer types)
let impl_15__overflowing_sub_unsigned (x: i64) (y: u64) : (i64 & bool) =
  let rhs:i64 = cast (y <: u64) <: i64 in
  let (result: i64), (overflowed: bool) = impl_15__overflowing_sub x rhs in
  result, overflowed <>. (rhs <. mk_i64 0 <: bool) <: (i64 & bool)

/// See [`std::primitive::i8::saturating_add_unsigned`] (and similar for other signed integer types)
let impl_15__saturating_add_unsigned (x: i64) (y: u64) : i64 =
  let (result: i64), (overflowed: bool) = impl_15__overflowing_add_unsigned x y in
  if overflowed then impl_15__MAX else result

/// See [`std::primitive::i8::saturating_sub_unsigned`] (and similar for other signed integer types)
let impl_15__saturating_sub_unsigned (x: i64) (y: u64) : i64 =
  let (result: i64), (overflowed: bool) = impl_15__overflowing_sub_unsigned x y in
  if overflowed then impl_15__MIN else result

/// See [`std::primitive::i8::reverse_bits`] (and similar for other signed integer types)
let impl_15__reverse_bits (x: i64) : i64 =
  cast (impl_9__reverse_bits (cast (x <: i64) <: u64) <: u64) <: i64

/// See [`std::primitive::i8::widening_mul`] (and similar for other signed integer types)
let impl_15__widening_mul (x y: i64) : (u64 & i64) =
  let (low: u64), (high: u64) =
    impl_9__widening_mul (cast (x <: i64) <: u64) (cast (y <: i64) <: u64)
  in
  let high:i64 = cast (high <: u64) <: i64 in
  let high:i64 = if x <. mk_i64 0 then impl_15__wrapping_sub high y else high in
  let high:i64 = if y <. mk_i64 0 then impl_15__wrapping_sub high x else high in
  low, high <: (u64 & i64)

/// See [`std::primitive::i8::carrying_mul_add`] (and similar for other signed integer types)
let impl_15__carrying_mul_add (x y carry add: i64) : (u64 & i64) =
  let (low: u64), (high: i64) = impl_15__widening_mul x y in
  let (low: u64), (c1: bool) = impl_9__overflowing_add low (cast (carry <: i64) <: u64) in
  let (low: u64), (c2: bool) = impl_9__overflowing_add low (cast (add <: i64) <: u64) in
  let high:i64 = impl_15__wrapping_add high (if c1 then mk_i64 1 else mk_i64 0) in
  let high:i64 = impl_15__wrapping_add high (if c2 then mk_i64 1 else mk_i64 0) in
  let high:i64 =
    impl_15__wrapping_add high (if carry <. mk_i64 0 <: bool then mk_i64 (-1) else mk_i64 0)
  in
  let high:i64 =
    impl_15__wrapping_add high (if add <. mk_i64 0 <: bool then mk_i64 (-1) else mk_i64 0)
  in
  low, high <: (u64 & i64)

/// See [`std::primitive::i8::carrying_mul`] (and similar for other signed integer types)
let impl_15__carrying_mul (x y carry: i64) : (u64 & i64) =
  impl_15__carrying_mul_add x y carry (mk_i64 0)

/// See [`std::primitive::i8::carrying_add`] (and similar for other integer types)
let impl_15__carrying_add (x y: i64) (carry: bool) : (i64 & bool) =
  let (a: i64), (b: bool) = impl_15__overflowing_add x y in
  let (c: i64), (d: bool) = impl_15__overflowing_add a (if carry then mk_i64 1 else mk_i64 0) in
  c, b <>. d <: (i64 & bool)

/// See [`std::primitive::i8::borrowing_sub`] (and similar for other integer types)
let impl_15__borrowing_sub (x y: i64) (borrow: bool) : (i64 & bool) =
  let (a: i64), (b: bool) = impl_15__overflowing_sub x y in
  let (c: i64), (d: bool) = impl_15__overflowing_sub a (if borrow then mk_i64 1 else mk_i64 0) in
  c, b <>. d <: (i64 & bool)

/// See [`std::primitive::i8::trailing_zeros`] (and similar for other integer types)
let impl_15__trailing_zeros (x: i64) : u32 =
  if x =. mk_i64 0
  then impl_15__BITS
  else
    impl_15__count_ones (impl_15__wrapping_sub (x &. (impl_15__wrapping_neg x <: i64) <: i64)
          (mk_i64 1)
        <:
        i64)

/// See [`std::primitive::i8::trailing_ones`] (and similar for other integer types)
let impl_15__trailing_ones (x: i64) : u32 =
  impl_15__trailing_zeros (impl_15__wrapping_sub (mk_i64 (-1)) x <: i64)

/// See [`std::primitive::i8::leading_ones`] (and similar for other integer types)
let impl_15__leading_ones (x: i64) : u32 =
  impl_15__leading_zeros (impl_15__wrapping_sub (mk_i64 (-1)) x <: i64)

/// See [`std::primitive::i8::isolate_lowest_one`] (and similar for other integer types)
let impl_15__isolate_lowest_one (x: i64) : i64 = x &. (impl_15__wrapping_neg x <: i64)

/// See [`std::primitive::i8::swap_bytes`] (and similar for other integer types)
let impl_15__swap_bytes (x: i64) : i64 =
  impl_15__from_le_bytes (impl_15__to_be_bytes x <: t_Array u8 (mk_usize 8))

/// See [`std::primitive::i8::to_be`] (and similar for other integer types)
let impl_15__to_be (x: i64) : i64 = impl_15__swap_bytes x

/// See [`std::primitive::i8::to_le`] (and similar for other integer types)
let impl_15__to_le (x: i64) : i64 = x

/// See [`std::primitive::i8::from_be`] (and similar for other integer types)
let impl_15__from_be (x: i64) : i64 = impl_15__swap_bytes x

/// See [`std::primitive::i8::from_le`] (and similar for other integer types)
let impl_15__from_le (x: i64) : i64 = x

/// See [`std::primitive::i8::to_ne_bytes`] (and similar for other integer types)
let impl_15__to_ne_bytes (x: i64) : t_Array u8 (mk_usize 8) = impl_15__to_le_bytes x

/// See [`std::primitive::i8::from_ne_bytes`] (and similar for other integer types)
let impl_15__from_ne_bytes (bytes: t_Array u8 (mk_usize 8)) : i64 = impl_15__from_le_bytes bytes

/// See [`std::primitive::i8::wrapping_shl`] (and similar for other integer types)
let impl_15__wrapping_shl (x: i64) (n: u32) : i64 = x <<! (n %! impl_15__BITS <: u32)

/// See [`std::primitive::i8::wrapping_shr`] (and similar for other integer types)
let impl_15__wrapping_shr (x: i64) (n: u32) : i64 = x >>! (n %! impl_15__BITS <: u32)

/// See [`std::primitive::i8::isolate_highest_one`] (and similar for other integer types)
let impl_15__isolate_highest_one (x: i64) : i64 =
  x &. (impl_15__wrapping_shr impl_15__MIN (impl_15__leading_zeros x <: u32) <: i64)

/// See [`std::primitive::i8::overflowing_shl`] (and similar for other integer types)
let impl_15__overflowing_shl (x: i64) (n: u32) : (i64 & bool) =
  impl_15__wrapping_shl x n, n >=. impl_15__BITS <: (i64 & bool)

/// See [`std::primitive::i8::overflowing_shr`] (and similar for other integer types)
let impl_15__overflowing_shr (x: i64) (n: u32) : (i64 & bool) =
  impl_15__wrapping_shr x n, n >=. impl_15__BITS <: (i64 & bool)

/// See [`std::primitive::i8::unbounded_shl`] (and similar for other integer types)
let impl_15__unbounded_shl (x: i64) (n: u32) : i64 =
  if n <. impl_15__BITS then x <<! n else mk_i64 0

/// See [`std::primitive::i8::unbounded_shr`] (and similar for other signed integer types)
let impl_15__unbounded_shr (x: i64) (n: u32) : i64 =
  if n <. impl_15__BITS then x >>! n else x >>! (impl_15__BITS -! mk_u32 1 <: u32)

/// See [`std::primitive::i8::clamp_magnitude`] (and similar for other signed integer types)
let impl_15__clamp_magnitude (x: i64) (limit: u64) : i64 =
  if limit >. (cast (impl_15__MAX <: i64) <: u64)
  then x
  else
    let hi:i64 = cast (limit <: u64) <: i64 in
    let lo:i64 = impl_15__wrapping_neg hi in
    if x <. lo then lo else if x >. hi then hi else x

/// See [`std::primitive::u8::unchecked_add`] (and similar for other integer types)
let impl_15__unchecked_add (x y: i64)
    : Prims.Pure i64
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_15__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_15__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) = x +! y

/// See [`std::primitive::u8::unchecked_sub`] (and similar for other integer types)
let impl_15__unchecked_sub (x y: i64)
    : Prims.Pure i64
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_15__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_15__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) = x -! y

/// See [`std::primitive::u8::unchecked_mul`] (and similar for other integer types)
let impl_15__unchecked_mul (x y: i64)
    : Prims.Pure i64
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_15__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_15__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) = x *! y

/// See [`std::primitive::u8::rem_euclid`] (and similar for other integer types)
let impl_15__rem_euclid (x y: i64)
    : Prims.Pure i64
      (requires y <>. mk_i64 0 && ~.((x =. impl_15__MIN <: bool) && (y =. mk_i64 (-1) <: bool)))
      (fun _ -> Prims.l_True) = Rust_primitives.Arithmetic.rem_euclid_i64 x y

/// See [`std::primitive::i8::abs`] (and similar for other signed integer types)
let impl_15__abs (x: i64) : Prims.Pure i64 (requires x >. impl_15__MIN) (fun _ -> Prims.l_True) =
  Rust_primitives.Arithmetic.abs_i64 x

/// See [`std::primitive::u8::unchecked_div`] (and similar for other integer types)
let impl_15__unchecked_div (x y: i64)
    : Prims.Pure i64
      (requires y <>. mk_i64 0 && (x <>. impl_15__MIN || y <>. mk_i64 (-1)))
      (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::unchecked_rem`] (and similar for other integer types)
let impl_15__unchecked_rem (x y: i64)
    : Prims.Pure i64
      (requires y <>. mk_i64 0 && (x <>. impl_15__MIN || y <>. mk_i64 (-1)))
      (fun _ -> Prims.l_True) = x %! y

/// See [`std::primitive::i8::div_ceil`] (and similar for other signed integer types)
let impl_15__div_ceil (x y: i64)
    : Prims.Pure i64
      (requires y <>. mk_i64 0 && ~.((x =. impl_15__MIN <: bool) && (y =. mk_i64 (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let d:i64 = x /! y in
  let r:i64 = x %! y in
  if r >. mk_i64 0 && y >. mk_i64 0 || r <. mk_i64 0 && y <. mk_i64 0 then d +! mk_i64 1 else d

/// See [`std::primitive::i8::strict_neg`] (and similar for other integer types)
let impl_15__strict_neg (x: i64)
    : Prims.Pure i64 (requires x <>. impl_15__MIN) (fun _ -> Prims.l_True) =
  if x =. impl_15__MIN
  then Core_models.Panicking.Internal.panic #i64 ()
  else impl_15__wrapping_neg x

/// See [`std::primitive::i8::unchecked_neg`] (and similar for other signed integer types)
let impl_15__unchecked_neg (x: i64)
    : Prims.Pure i64 (requires x <>. impl_15__MIN) (fun _ -> Prims.l_True) = mk_i64 0 -! x

/// See [`std::primitive::i8::strict_abs`] (and similar for other signed integer types)
let impl_15__strict_abs (x: i64)
    : Prims.Pure i64 (requires x <>. impl_15__MIN) (fun _ -> Prims.l_True) =
  if x <. mk_i64 0 then impl_15__strict_neg x else x

/// See [`std::primitive::i8::strict_pow`] (and similar for other integer types)
let impl_15__strict_pow (x: i64) (exp: u32)
    : Prims.Pure i64
      (requires (impl_15__overflowing_pow x exp <: (i64 & bool))._2 =. false)
      (fun _ -> Prims.l_True) =
  let (result: i64), (overflowed: bool) = impl_15__overflowing_pow x exp in
  if overflowed then Core_models.Panicking.Internal.panic #i64 () else result

/// See [`std::primitive::i8::strict_add`] (and similar for other integer types)
let impl_15__strict_add (x y: i64)
    : Prims.Pure i64
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_15__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_15__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: i64), (overflowed: bool) = impl_15__overflowing_add x y in
  if overflowed then Core_models.Panicking.Internal.panic #i64 () else result

/// See [`std::primitive::i8::strict_sub`] (and similar for other integer types)
let impl_15__strict_sub (x y: i64)
    : Prims.Pure i64
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_15__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_15__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: i64), (overflowed: bool) = impl_15__overflowing_sub x y in
  if overflowed then Core_models.Panicking.Internal.panic #i64 () else result

/// See [`std::primitive::i8::strict_mul`] (and similar for other integer types)
let impl_15__strict_mul (x y: i64)
    : Prims.Pure i64
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_15__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_15__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: i64), (overflowed: bool) = impl_15__overflowing_mul x y in
  if overflowed then Core_models.Panicking.Internal.panic #i64 () else result

/// See [`std::primitive::i8::overflowing_div`] (and similar for other signed integer types)
let impl_15__overflowing_div (x y: i64)
    : Prims.Pure (i64 & bool) (requires y <>. mk_i64 0) (fun _ -> Prims.l_True) =
  if x =. impl_15__MIN && y =. mk_i64 (-1)
  then x, true <: (i64 & bool)
  else x /! y, false <: (i64 & bool)

/// See [`std::primitive::i8::overflowing_rem`] (and similar for other signed integer types)
let impl_15__overflowing_rem (x y: i64)
    : Prims.Pure (i64 & bool) (requires y <>. mk_i64 0) (fun _ -> Prims.l_True) =
  if y =. mk_i64 (-1)
  then mk_i64 0, x =. impl_15__MIN <: (i64 & bool)
  else x %! y, false <: (i64 & bool)

/// See [`std::primitive::i8::wrapping_div`] (and similar for other signed integer types)
let impl_15__wrapping_div (x y: i64)
    : Prims.Pure i64 (requires y <>. mk_i64 0) (fun _ -> Prims.l_True) =
  let (result: i64), (_: bool) = impl_15__overflowing_div x y in
  result

/// See [`std::primitive::i8::wrapping_rem`] (and similar for other signed integer types)
let impl_15__wrapping_rem (x y: i64)
    : Prims.Pure i64 (requires y <>. mk_i64 0) (fun _ -> Prims.l_True) =
  let (result: i64), (_: bool) = impl_15__overflowing_rem x y in
  result

/// See [`std::primitive::i8::saturating_div`] (and similar for other signed integer types)
let impl_15__saturating_div (x y: i64)
    : Prims.Pure i64 (requires y <>. mk_i64 0) (fun _ -> Prims.l_True) =
  let (result: i64), (overflowed: bool) = impl_15__overflowing_div x y in
  if overflowed then impl_15__MAX else result

/// See [`std::primitive::i8::strict_div`] (and similar for other signed integer types)
let impl_15__strict_div (x y: i64)
    : Prims.Pure i64
      (requires y <>. mk_i64 0 && ~.((x =. impl_15__MIN <: bool) && (y =. mk_i64 (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let (result: i64), (overflowed: bool) = impl_15__overflowing_div x y in
  if overflowed then Core_models.Panicking.Internal.panic #i64 () else result

/// See [`std::primitive::i8::strict_rem`] (and similar for other signed integer types)
let impl_15__strict_rem (x y: i64)
    : Prims.Pure i64
      (requires y <>. mk_i64 0 && ~.((x =. impl_15__MIN <: bool) && (y =. mk_i64 (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let (result: i64), (overflowed: bool) = impl_15__overflowing_rem x y in
  if overflowed then Core_models.Panicking.Internal.panic #i64 () else result

/// See [`std::primitive::i8::div_euclid`] (and similar for other signed integer types)
let impl_15__div_euclid (x y: i64)
    : Prims.Pure i64
      (requires y <>. mk_i64 0 && ~.((x =. impl_15__MIN <: bool) && (y =. mk_i64 (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let q:i64 = x /! y in
  if (x %! y <: i64) <. mk_i64 0
  then
    if y >. mk_i64 0 then impl_15__wrapping_sub q (mk_i64 1) else impl_15__wrapping_add q (mk_i64 1)
  else q

/// See [`std::primitive::i8::overflowing_div_euclid`] (and similar for other signed integer types)
let impl_15__overflowing_div_euclid (x y: i64)
    : Prims.Pure (i64 & bool) (requires y <>. mk_i64 0) (fun _ -> Prims.l_True) =
  if x =. impl_15__MIN && y =. mk_i64 (-1)
  then x, true <: (i64 & bool)
  else impl_15__div_euclid x y, false <: (i64 & bool)

/// See [`std::primitive::i8::wrapping_div_euclid`] (and similar for other signed integer types)
let impl_15__wrapping_div_euclid (x y: i64)
    : Prims.Pure i64 (requires y <>. mk_i64 0) (fun _ -> Prims.l_True) =
  let (result: i64), (_: bool) = impl_15__overflowing_div_euclid x y in
  result

/// See [`std::primitive::i8::strict_div_euclid`] (and similar for other signed integer types)
let impl_15__strict_div_euclid (x y: i64)
    : Prims.Pure i64
      (requires y <>. mk_i64 0 && ~.((x =. impl_15__MIN <: bool) && (y =. mk_i64 (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let (result: i64), (overflowed: bool) = impl_15__overflowing_div_euclid x y in
  if overflowed then Core_models.Panicking.Internal.panic #i64 () else result

/// See [`std::primitive::i8::overflowing_rem_euclid`] (and similar for other signed integer types)
let impl_15__overflowing_rem_euclid (x y: i64)
    : Prims.Pure (i64 & bool) (requires y <>. mk_i64 0) (fun _ -> Prims.l_True) =
  if y =. mk_i64 (-1)
  then mk_i64 0, x =. impl_15__MIN <: (i64 & bool)
  else impl_15__rem_euclid x y, false <: (i64 & bool)

/// See [`std::primitive::i8::wrapping_rem_euclid`] (and similar for other signed integer types)
let impl_15__wrapping_rem_euclid (x y: i64)
    : Prims.Pure i64 (requires y <>. mk_i64 0) (fun _ -> Prims.l_True) =
  let (result: i64), (_: bool) = impl_15__overflowing_rem_euclid x y in
  result

/// See [`std::primitive::i8::strict_rem_euclid`] (and similar for other signed integer types)
let impl_15__strict_rem_euclid (x y: i64)
    : Prims.Pure i64
      (requires y <>. mk_i64 0 && ~.((x =. impl_15__MIN <: bool) && (y =. mk_i64 (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let (result: i64), (overflowed: bool) = impl_15__overflowing_rem_euclid x y in
  if overflowed then Core_models.Panicking.Internal.panic #i64 () else result

/// See [`std::primitive::i8::div_floor`] (and similar for other signed integer types)
let impl_15__div_floor (x y: i64)
    : Prims.Pure i64
      (requires y <>. mk_i64 0 && ~.((x =. impl_15__MIN <: bool) && (y =. mk_i64 (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let d:i64 = x /! y in
  let r:i64 = x %! y in
  if r <>. mk_i64 0 && (x <. mk_i64 0 <: bool) <>. (y <. mk_i64 0 <: bool)
  then impl_15__wrapping_sub d (mk_i64 1)
  else d

/// See [`std::primitive::i8::unchecked_div_exact`] (and similar for other signed integer types)
let impl_15__unchecked_div_exact (x y: i64)
    : Prims.Pure i64 (requires y >. mk_i64 0 && (x %! y <: i64) =. mk_i64 0) (fun _ -> Prims.l_True) =
  x /! y

/// See [`std::primitive::i8::strict_add_unsigned`] (and similar for other signed integer types)
let impl_15__strict_add_unsigned (x: i64) (y: u64)
    : Prims.Pure i64
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_15__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: i64), (overflowed: bool) = impl_15__overflowing_add_unsigned x y in
  if overflowed then Core_models.Panicking.Internal.panic #i64 () else result

/// See [`std::primitive::i8::strict_sub_unsigned`] (and similar for other signed integer types)
let impl_15__strict_sub_unsigned (x: i64) (y: u64)
    : Prims.Pure i64
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_15__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: i64), (overflowed: bool) = impl_15__overflowing_sub_unsigned x y in
  if overflowed then Core_models.Panicking.Internal.panic #i64 () else result

/// See [`std::primitive::i8::strict_shl`] (and similar for other integer types)
let impl_15__strict_shl (x: i64) (n: u32)
    : Prims.Pure i64 (requires n <. impl_15__BITS) (fun _ -> Prims.l_True) =
  if n <. impl_15__BITS then x <<! n else Core_models.Panicking.Internal.panic #i64 ()

/// See [`std::primitive::i8::strict_shr`] (and similar for other integer types)
let impl_15__strict_shr (x: i64) (n: u32)
    : Prims.Pure i64 (requires n <. impl_15__BITS) (fun _ -> Prims.l_True) =
  if n <. impl_15__BITS then x >>! n else Core_models.Panicking.Internal.panic #i64 ()

/// See [`std::primitive::i8::unchecked_shl`] (and similar for other integer types)
let impl_15__unchecked_shl (x: i64) (n: u32)
    : Prims.Pure i64 (requires n <. impl_15__BITS) (fun _ -> Prims.l_True) = x <<! n

/// See [`std::primitive::i8::unchecked_shr`] (and similar for other integer types)
let impl_15__unchecked_shr (x: i64) (n: u32)
    : Prims.Pure i64 (requires n <. impl_15__BITS) (fun _ -> Prims.l_True) = x >>! n

/// See [`std::primitive::i8::unchecked_shl_exact`] (and similar for other signed integer types)
let impl_15__unchecked_shl_exact (x: i64) (n: u32)
    : Prims.Pure i64
      (requires
        (n <. (impl_15__leading_zeros x <: u32) || n <. (impl_15__leading_ones x <: u32)) &&
        n <. impl_15__BITS)
      (fun _ -> Prims.l_True) = x <<! n

/// See [`std::primitive::i8::unchecked_shr_exact`] (and similar for other integer types)
let impl_15__unchecked_shr_exact (x: i64) (n: u32)
    : Prims.Pure i64
      (requires n <=. (impl_15__trailing_zeros x <: u32) && n <. impl_15__BITS)
      (fun _ -> Prims.l_True) = x >>! n

/// See [`std::primitive::i8::MIN`] (and similar for other signed integer types)
let impl_16__MIN: i128 = mk_i128 (-170141183460469231731687303715884105728)

/// See [`std::primitive::i8::MAX`] (and similar for other signed integer types)
let impl_16__MAX: i128 = mk_i128 170141183460469231731687303715884105727

/// See [`std::primitive::i8::BITS`] (and similar for other signed integer types)
let impl_16__BITS: u32 = mk_u32 128

let impl_16__wrapping_add (x y: i128) : i128 = Rust_primitives.Arithmetic.wrapping_add_i128 x y

/// See [`std::primitive::u8::saturating_add`] (and similar for other integer types)
let impl_16__saturating_add (x y: i128) : i128 = Rust_primitives.Arithmetic.saturating_add_i128 x y

/// See [`std::primitive::u8::overflowing_add`] (and similar for other integer types)
let impl_16__overflowing_add (x y: i128) : (i128 & bool) =
  Rust_primitives.Arithmetic.overflowing_add_i128 x y

/// See [`std::primitive::u8::wrapping_sub`] (and similar for other integer types)
let impl_16__wrapping_sub (x y: i128) : i128 = Rust_primitives.Arithmetic.wrapping_sub_i128 x y

/// See [`std::primitive::u8::saturating_sub`] (and similar for other integer types)
let impl_16__saturating_sub (x y: i128) : i128 = Rust_primitives.Arithmetic.saturating_sub_i128 x y

/// See [`std::primitive::u8::overflowing_sub`] (and similar for other integer types)
let impl_16__overflowing_sub (x y: i128) : (i128 & bool) =
  Rust_primitives.Arithmetic.overflowing_sub_i128 x y

/// See [`std::primitive::u8::wrapping_mul`] (and similar for other integer types)
let impl_16__wrapping_mul (x y: i128) : i128 = Rust_primitives.Arithmetic.wrapping_mul_i128 x y

/// See [`std::primitive::u8::saturating_mul`] (and similar for other integer types)
let impl_16__saturating_mul (x y: i128) : i128 = Rust_primitives.Arithmetic.saturating_mul_i128 x y

/// See [`std::primitive::u8::overflowing_mul`] (and similar for other integer types)
let impl_16__overflowing_mul (x y: i128) : (i128 & bool) =
  Rust_primitives.Arithmetic.overflowing_mul_i128 x y

/// See [`std::primitive::u8::pow`] (and similar for other integer types)
let impl_16__pow (x: i128) (exp: u32) : i128 = Rust_primitives.Arithmetic.pow_i128 x exp

/// See [`std::primitive::u8::overflowing_pow`] (and similar for other integer types)
let impl_16__overflowing_pow (x: i128) (exp: u32) : (i128 & bool) =
  Rust_primitives.Arithmetic.overflowing_pow_i128 x exp

/// See [`std::primitive::u8::count_ones`] (and similar for other integer types)
let impl_16__count_ones (x: i128) : u32 = Rust_primitives.Arithmetic.count_ones_i128 x

/// See [`std::primitive::u8::rotate_right`] (and similar for other integer types)
assume
val impl_16__rotate_right': x: i128 -> n: u32 -> i128

unfold
let impl_16__rotate_right = impl_16__rotate_right'

/// See [`std::primitive::u8::rotate_left`] (and similar for other integer types)
assume
val impl_16__rotate_left': x: i128 -> n: u32 -> i128

unfold
let impl_16__rotate_left = impl_16__rotate_left'

/// See [`std::primitive::u8::leading_zeros`] (and similar for other integer types)
assume
val impl_16__leading_zeros': x: i128 -> u32

unfold
let impl_16__leading_zeros = impl_16__leading_zeros'

/// See [`std::primitive::u8::ilog2`] (and similar for other integer types)
assume
val impl_16__ilog2': x: i128 -> u32

unfold
let impl_16__ilog2 = impl_16__ilog2'

/// See [`std::primitive::u8::from_be_bytes`] (and similar for other integer types)
assume
val impl_16__from_be_bytes': bytes: t_Array u8 (mk_usize 16) -> i128

unfold
let impl_16__from_be_bytes = impl_16__from_be_bytes'

/// See [`std::primitive::u8::from_le_bytes`] (and similar for other integer types)
assume
val impl_16__from_le_bytes': bytes: t_Array u8 (mk_usize 16) -> i128

unfold
let impl_16__from_le_bytes = impl_16__from_le_bytes'

/// See [`std::primitive::u8::to_be_bytes`] (and similar for other integer types)
assume
val impl_16__to_be_bytes': bytes: i128 -> t_Array u8 (mk_usize 16)

unfold
let impl_16__to_be_bytes = impl_16__to_be_bytes'

/// See [`std::primitive::u8::to_le_bytes`] (and similar for other integer types)
assume
val impl_16__to_le_bytes': bytes: i128 -> t_Array u8 (mk_usize 16)

unfold
let impl_16__to_le_bytes = impl_16__to_le_bytes'

/// See [`std::primitive::i8::signum`] (and similar for other signed integer types)
let impl_16__signum (x: i128) : i128 =
  if x >. mk_i128 0 then mk_i128 1 else if x =. mk_i128 0 then mk_i128 0 else mk_i128 (-1)

/// See [`std::primitive::i8::wrapping_neg`] (and similar for other signed integer types)
let impl_16__wrapping_neg (x: i128) : i128 =
  Rust_primitives.Arithmetic.wrapping_sub_i128 (mk_i128 0) x

/// See [`std::primitive::i8::min_value`] (and similar for other integer types)
let impl_16__min_value (_: Prims.unit) : i128 = impl_16__MIN

/// See [`std::primitive::i8::max_value`] (and similar for other integer types)
let impl_16__max_value (_: Prims.unit) : i128 = impl_16__MAX

/// See [`std::primitive::i8::cast_unsigned`] (and similar for other signed integer types)
let impl_16__cast_unsigned (x: i128) : u128 = cast (x <: i128) <: u128

/// See [`std::primitive::i8::is_positive`] (and similar for other signed integer types)
let impl_16__is_positive (x: i128) : bool = x >. mk_i128 0

/// See [`std::primitive::i8::is_negative`] (and similar for other signed integer types)
let impl_16__is_negative (x: i128) : bool = x <. mk_i128 0

/// See [`std::primitive::i8::count_zeros`] (and similar for other integer types)
let impl_16__count_zeros (x: i128) : u32 = impl_16__BITS -! (impl_16__count_ones x <: u32)

/// See [`std::primitive::i8::overflowing_neg`] (and similar for other integer types)
let impl_16__overflowing_neg (x: i128) : (i128 & bool) =
  if x =. impl_16__MIN
  then impl_16__MIN, true <: (i128 & bool)
  else impl_16__wrapping_neg x, false <: (i128 & bool)

/// See [`std::primitive::i8::saturating_neg`] (and similar for other signed integer types)
let impl_16__saturating_neg (x: i128) : i128 =
  if x =. impl_16__MIN then impl_16__MAX else impl_16__wrapping_neg x

/// See [`std::primitive::i8::wrapping_abs`] (and similar for other signed integer types)
let impl_16__wrapping_abs (x: i128) : i128 = if x <. mk_i128 0 then impl_16__wrapping_neg x else x

/// See [`std::primitive::i8::overflowing_abs`] (and similar for other signed integer types)
let impl_16__overflowing_abs (x: i128) : (i128 & bool) =
  impl_16__wrapping_abs x, x =. impl_16__MIN <: (i128 & bool)

/// See [`std::primitive::i8::saturating_abs`] (and similar for other signed integer types)
let impl_16__saturating_abs (x: i128) : i128 =
  if x <. mk_i128 0 then impl_16__saturating_neg x else x

/// See [`std::primitive::i8::unsigned_abs`] (and similar for other signed integer types)
let impl_16__unsigned_abs (x: i128) : u128 = cast (impl_16__wrapping_abs x <: i128) <: u128

/// See [`std::primitive::i8::wrapping_pow`] (and similar for other integer types)
let impl_16__wrapping_pow (x: i128) (exp: u32) : i128 =
  let (result: i128), (_: bool) = impl_16__overflowing_pow x exp in
  result

/// See [`std::primitive::i8::saturating_pow`] (and similar for other signed integer types)
let impl_16__saturating_pow (x: i128) (exp: u32) : i128 =
  let (result: i128), (overflowed: bool) = impl_16__overflowing_pow x exp in
  if ~.overflowed
  then result
  else if x <. mk_i128 0 && (exp %! mk_u32 2 <: u32) =. mk_u32 1 then impl_16__MIN else impl_16__MAX

/// See [`std::primitive::i8::abs_diff`] (and similar for other signed integer types)
let impl_16__abs_diff (x y: i128) : u128 =
  if x <. y
  then cast (impl_16__wrapping_sub y x <: i128) <: u128
  else cast (impl_16__wrapping_sub x y <: i128) <: u128

/// See [`std::primitive::i8::midpoint`] (and similar for other signed integer types)
let impl_16__midpoint (x y: i128) : i128 =
  let d:i128 = x ^. y in
  let t:i128 = impl_16__wrapping_add (d >>! mk_i32 1 <: i128) (x &. y <: i128) in
  if t <. mk_i128 0 then impl_16__wrapping_add t (d &. mk_i128 1 <: i128) else t

/// See [`std::primitive::i8::wrapping_add_unsigned`] (and similar for other signed integer types)
let impl_16__wrapping_add_unsigned (x: i128) (y: u128) : i128 =
  impl_16__wrapping_add x (cast (y <: u128) <: i128)

/// See [`std::primitive::i8::wrapping_sub_unsigned`] (and similar for other signed integer types)
let impl_16__wrapping_sub_unsigned (x: i128) (y: u128) : i128 =
  impl_16__wrapping_sub x (cast (y <: u128) <: i128)

/// See [`std::primitive::i8::overflowing_add_unsigned`] (and similar for other signed integer types)
let impl_16__overflowing_add_unsigned (x: i128) (y: u128) : (i128 & bool) =
  let rhs:i128 = cast (y <: u128) <: i128 in
  let (result: i128), (overflowed: bool) = impl_16__overflowing_add x rhs in
  result, overflowed <>. (rhs <. mk_i128 0 <: bool) <: (i128 & bool)

/// See [`std::primitive::i8::overflowing_sub_unsigned`] (and similar for other signed integer types)
let impl_16__overflowing_sub_unsigned (x: i128) (y: u128) : (i128 & bool) =
  let rhs:i128 = cast (y <: u128) <: i128 in
  let (result: i128), (overflowed: bool) = impl_16__overflowing_sub x rhs in
  result, overflowed <>. (rhs <. mk_i128 0 <: bool) <: (i128 & bool)

/// See [`std::primitive::i8::saturating_add_unsigned`] (and similar for other signed integer types)
let impl_16__saturating_add_unsigned (x: i128) (y: u128) : i128 =
  let (result: i128), (overflowed: bool) = impl_16__overflowing_add_unsigned x y in
  if overflowed then impl_16__MAX else result

/// See [`std::primitive::i8::saturating_sub_unsigned`] (and similar for other signed integer types)
let impl_16__saturating_sub_unsigned (x: i128) (y: u128) : i128 =
  let (result: i128), (overflowed: bool) = impl_16__overflowing_sub_unsigned x y in
  if overflowed then impl_16__MIN else result

/// See [`std::primitive::i8::reverse_bits`] (and similar for other signed integer types)
let impl_16__reverse_bits (x: i128) : i128 =
  cast (impl_10__reverse_bits (cast (x <: i128) <: u128) <: u128) <: i128

/// See [`std::primitive::i8::widening_mul`] (and similar for other signed integer types)
let impl_16__widening_mul (x y: i128) : (u128 & i128) =
  let (low: u128), (high: u128) =
    impl_10__widening_mul (cast (x <: i128) <: u128) (cast (y <: i128) <: u128)
  in
  let high:i128 = cast (high <: u128) <: i128 in
  let high:i128 = if x <. mk_i128 0 then impl_16__wrapping_sub high y else high in
  let high:i128 = if y <. mk_i128 0 then impl_16__wrapping_sub high x else high in
  low, high <: (u128 & i128)

/// See [`std::primitive::i8::carrying_mul_add`] (and similar for other signed integer types)
let impl_16__carrying_mul_add (x y carry add: i128) : (u128 & i128) =
  let (low: u128), (high: i128) = impl_16__widening_mul x y in
  let (low: u128), (c1: bool) = impl_10__overflowing_add low (cast (carry <: i128) <: u128) in
  let (low: u128), (c2: bool) = impl_10__overflowing_add low (cast (add <: i128) <: u128) in
  let high:i128 = impl_16__wrapping_add high (if c1 then mk_i128 1 else mk_i128 0) in
  let high:i128 = impl_16__wrapping_add high (if c2 then mk_i128 1 else mk_i128 0) in
  let high:i128 =
    impl_16__wrapping_add high (if carry <. mk_i128 0 <: bool then mk_i128 (-1) else mk_i128 0)
  in
  let high:i128 =
    impl_16__wrapping_add high (if add <. mk_i128 0 <: bool then mk_i128 (-1) else mk_i128 0)
  in
  low, high <: (u128 & i128)

/// See [`std::primitive::i8::carrying_mul`] (and similar for other signed integer types)
let impl_16__carrying_mul (x y carry: i128) : (u128 & i128) =
  impl_16__carrying_mul_add x y carry (mk_i128 0)

/// See [`std::primitive::i8::carrying_add`] (and similar for other integer types)
let impl_16__carrying_add (x y: i128) (carry: bool) : (i128 & bool) =
  let (a: i128), (b: bool) = impl_16__overflowing_add x y in
  let (c: i128), (d: bool) = impl_16__overflowing_add a (if carry then mk_i128 1 else mk_i128 0) in
  c, b <>. d <: (i128 & bool)

/// See [`std::primitive::i8::borrowing_sub`] (and similar for other integer types)
let impl_16__borrowing_sub (x y: i128) (borrow: bool) : (i128 & bool) =
  let (a: i128), (b: bool) = impl_16__overflowing_sub x y in
  let (c: i128), (d: bool) = impl_16__overflowing_sub a (if borrow then mk_i128 1 else mk_i128 0) in
  c, b <>. d <: (i128 & bool)

/// See [`std::primitive::i8::trailing_zeros`] (and similar for other integer types)
let impl_16__trailing_zeros (x: i128) : u32 =
  if x =. mk_i128 0
  then impl_16__BITS
  else
    impl_16__count_ones (impl_16__wrapping_sub (x &. (impl_16__wrapping_neg x <: i128) <: i128)
          (mk_i128 1)
        <:
        i128)

/// See [`std::primitive::i8::trailing_ones`] (and similar for other integer types)
let impl_16__trailing_ones (x: i128) : u32 =
  impl_16__trailing_zeros (impl_16__wrapping_sub (mk_i128 (-1)) x <: i128)

/// See [`std::primitive::i8::leading_ones`] (and similar for other integer types)
let impl_16__leading_ones (x: i128) : u32 =
  impl_16__leading_zeros (impl_16__wrapping_sub (mk_i128 (-1)) x <: i128)

/// See [`std::primitive::i8::isolate_lowest_one`] (and similar for other integer types)
let impl_16__isolate_lowest_one (x: i128) : i128 = x &. (impl_16__wrapping_neg x <: i128)

/// See [`std::primitive::i8::swap_bytes`] (and similar for other integer types)
let impl_16__swap_bytes (x: i128) : i128 =
  impl_16__from_le_bytes (impl_16__to_be_bytes x <: t_Array u8 (mk_usize 16))

/// See [`std::primitive::i8::to_be`] (and similar for other integer types)
let impl_16__to_be (x: i128) : i128 = impl_16__swap_bytes x

/// See [`std::primitive::i8::to_le`] (and similar for other integer types)
let impl_16__to_le (x: i128) : i128 = x

/// See [`std::primitive::i8::from_be`] (and similar for other integer types)
let impl_16__from_be (x: i128) : i128 = impl_16__swap_bytes x

/// See [`std::primitive::i8::from_le`] (and similar for other integer types)
let impl_16__from_le (x: i128) : i128 = x

/// See [`std::primitive::i8::to_ne_bytes`] (and similar for other integer types)
let impl_16__to_ne_bytes (x: i128) : t_Array u8 (mk_usize 16) = impl_16__to_le_bytes x

/// See [`std::primitive::i8::from_ne_bytes`] (and similar for other integer types)
let impl_16__from_ne_bytes (bytes: t_Array u8 (mk_usize 16)) : i128 = impl_16__from_le_bytes bytes

/// See [`std::primitive::i8::wrapping_shl`] (and similar for other integer types)
let impl_16__wrapping_shl (x: i128) (n: u32) : i128 = x <<! (n %! impl_16__BITS <: u32)

/// See [`std::primitive::i8::wrapping_shr`] (and similar for other integer types)
let impl_16__wrapping_shr (x: i128) (n: u32) : i128 = x >>! (n %! impl_16__BITS <: u32)

/// See [`std::primitive::i8::isolate_highest_one`] (and similar for other integer types)
let impl_16__isolate_highest_one (x: i128) : i128 =
  x &. (impl_16__wrapping_shr impl_16__MIN (impl_16__leading_zeros x <: u32) <: i128)

/// See [`std::primitive::i8::overflowing_shl`] (and similar for other integer types)
let impl_16__overflowing_shl (x: i128) (n: u32) : (i128 & bool) =
  impl_16__wrapping_shl x n, n >=. impl_16__BITS <: (i128 & bool)

/// See [`std::primitive::i8::overflowing_shr`] (and similar for other integer types)
let impl_16__overflowing_shr (x: i128) (n: u32) : (i128 & bool) =
  impl_16__wrapping_shr x n, n >=. impl_16__BITS <: (i128 & bool)

/// See [`std::primitive::i8::unbounded_shl`] (and similar for other integer types)
let impl_16__unbounded_shl (x: i128) (n: u32) : i128 =
  if n <. impl_16__BITS then x <<! n else mk_i128 0

/// See [`std::primitive::i8::unbounded_shr`] (and similar for other signed integer types)
let impl_16__unbounded_shr (x: i128) (n: u32) : i128 =
  if n <. impl_16__BITS then x >>! n else x >>! (impl_16__BITS -! mk_u32 1 <: u32)

/// See [`std::primitive::i8::clamp_magnitude`] (and similar for other signed integer types)
let impl_16__clamp_magnitude (x: i128) (limit: u128) : i128 =
  if limit >. (cast (impl_16__MAX <: i128) <: u128)
  then x
  else
    let hi:i128 = cast (limit <: u128) <: i128 in
    let lo:i128 = impl_16__wrapping_neg hi in
    if x <. lo then lo else if x >. hi then hi else x

/// See [`std::primitive::u8::unchecked_add`] (and similar for other integer types)
let impl_16__unchecked_add (x y: i128)
    : Prims.Pure i128
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_16__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_16__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) = x +! y

/// See [`std::primitive::u8::unchecked_sub`] (and similar for other integer types)
let impl_16__unchecked_sub (x y: i128)
    : Prims.Pure i128
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_16__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_16__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) = x -! y

/// See [`std::primitive::u8::unchecked_mul`] (and similar for other integer types)
let impl_16__unchecked_mul (x y: i128)
    : Prims.Pure i128
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_16__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_16__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) = x *! y

/// See [`std::primitive::u8::rem_euclid`] (and similar for other integer types)
let impl_16__rem_euclid (x y: i128)
    : Prims.Pure i128
      (requires y <>. mk_i128 0 && ~.((x =. impl_16__MIN <: bool) && (y =. mk_i128 (-1) <: bool)))
      (fun _ -> Prims.l_True) = Rust_primitives.Arithmetic.rem_euclid_i128 x y

/// See [`std::primitive::i8::abs`] (and similar for other signed integer types)
let impl_16__abs (x: i128) : Prims.Pure i128 (requires x >. impl_16__MIN) (fun _ -> Prims.l_True) =
  Rust_primitives.Arithmetic.abs_i128 x

/// See [`std::primitive::u8::unchecked_div`] (and similar for other integer types)
let impl_16__unchecked_div (x y: i128)
    : Prims.Pure i128
      (requires y <>. mk_i128 0 && (x <>. impl_16__MIN || y <>. mk_i128 (-1)))
      (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::unchecked_rem`] (and similar for other integer types)
let impl_16__unchecked_rem (x y: i128)
    : Prims.Pure i128
      (requires y <>. mk_i128 0 && (x <>. impl_16__MIN || y <>. mk_i128 (-1)))
      (fun _ -> Prims.l_True) = x %! y

/// See [`std::primitive::i8::div_ceil`] (and similar for other signed integer types)
let impl_16__div_ceil (x y: i128)
    : Prims.Pure i128
      (requires y <>. mk_i128 0 && ~.((x =. impl_16__MIN <: bool) && (y =. mk_i128 (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let d:i128 = x /! y in
  let r:i128 = x %! y in
  if r >. mk_i128 0 && y >. mk_i128 0 || r <. mk_i128 0 && y <. mk_i128 0 then d +! mk_i128 1 else d

/// See [`std::primitive::i8::strict_neg`] (and similar for other integer types)
let impl_16__strict_neg (x: i128)
    : Prims.Pure i128 (requires x <>. impl_16__MIN) (fun _ -> Prims.l_True) =
  if x =. impl_16__MIN
  then Core_models.Panicking.Internal.panic #i128 ()
  else impl_16__wrapping_neg x

/// See [`std::primitive::i8::unchecked_neg`] (and similar for other signed integer types)
let impl_16__unchecked_neg (x: i128)
    : Prims.Pure i128 (requires x <>. impl_16__MIN) (fun _ -> Prims.l_True) = mk_i128 0 -! x

/// See [`std::primitive::i8::strict_abs`] (and similar for other signed integer types)
let impl_16__strict_abs (x: i128)
    : Prims.Pure i128 (requires x <>. impl_16__MIN) (fun _ -> Prims.l_True) =
  if x <. mk_i128 0 then impl_16__strict_neg x else x

/// See [`std::primitive::i8::strict_pow`] (and similar for other integer types)
let impl_16__strict_pow (x: i128) (exp: u32)
    : Prims.Pure i128
      (requires (impl_16__overflowing_pow x exp <: (i128 & bool))._2 =. false)
      (fun _ -> Prims.l_True) =
  let (result: i128), (overflowed: bool) = impl_16__overflowing_pow x exp in
  if overflowed then Core_models.Panicking.Internal.panic #i128 () else result

/// See [`std::primitive::i8::strict_add`] (and similar for other integer types)
let impl_16__strict_add (x y: i128)
    : Prims.Pure i128
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_16__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_16__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: i128), (overflowed: bool) = impl_16__overflowing_add x y in
  if overflowed then Core_models.Panicking.Internal.panic #i128 () else result

/// See [`std::primitive::i8::strict_sub`] (and similar for other integer types)
let impl_16__strict_sub (x y: i128)
    : Prims.Pure i128
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_16__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_16__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: i128), (overflowed: bool) = impl_16__overflowing_sub x y in
  if overflowed then Core_models.Panicking.Internal.panic #i128 () else result

/// See [`std::primitive::i8::strict_mul`] (and similar for other integer types)
let impl_16__strict_mul (x y: i128)
    : Prims.Pure i128
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_16__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_16__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: i128), (overflowed: bool) = impl_16__overflowing_mul x y in
  if overflowed then Core_models.Panicking.Internal.panic #i128 () else result

/// See [`std::primitive::i8::overflowing_div`] (and similar for other signed integer types)
let impl_16__overflowing_div (x y: i128)
    : Prims.Pure (i128 & bool) (requires y <>. mk_i128 0) (fun _ -> Prims.l_True) =
  if x =. impl_16__MIN && y =. mk_i128 (-1)
  then x, true <: (i128 & bool)
  else x /! y, false <: (i128 & bool)

/// See [`std::primitive::i8::overflowing_rem`] (and similar for other signed integer types)
let impl_16__overflowing_rem (x y: i128)
    : Prims.Pure (i128 & bool) (requires y <>. mk_i128 0) (fun _ -> Prims.l_True) =
  if y =. mk_i128 (-1)
  then mk_i128 0, x =. impl_16__MIN <: (i128 & bool)
  else x %! y, false <: (i128 & bool)

/// See [`std::primitive::i8::wrapping_div`] (and similar for other signed integer types)
let impl_16__wrapping_div (x y: i128)
    : Prims.Pure i128 (requires y <>. mk_i128 0) (fun _ -> Prims.l_True) =
  let (result: i128), (_: bool) = impl_16__overflowing_div x y in
  result

/// See [`std::primitive::i8::wrapping_rem`] (and similar for other signed integer types)
let impl_16__wrapping_rem (x y: i128)
    : Prims.Pure i128 (requires y <>. mk_i128 0) (fun _ -> Prims.l_True) =
  let (result: i128), (_: bool) = impl_16__overflowing_rem x y in
  result

/// See [`std::primitive::i8::saturating_div`] (and similar for other signed integer types)
let impl_16__saturating_div (x y: i128)
    : Prims.Pure i128 (requires y <>. mk_i128 0) (fun _ -> Prims.l_True) =
  let (result: i128), (overflowed: bool) = impl_16__overflowing_div x y in
  if overflowed then impl_16__MAX else result

/// See [`std::primitive::i8::strict_div`] (and similar for other signed integer types)
let impl_16__strict_div (x y: i128)
    : Prims.Pure i128
      (requires y <>. mk_i128 0 && ~.((x =. impl_16__MIN <: bool) && (y =. mk_i128 (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let (result: i128), (overflowed: bool) = impl_16__overflowing_div x y in
  if overflowed then Core_models.Panicking.Internal.panic #i128 () else result

/// See [`std::primitive::i8::strict_rem`] (and similar for other signed integer types)
let impl_16__strict_rem (x y: i128)
    : Prims.Pure i128
      (requires y <>. mk_i128 0 && ~.((x =. impl_16__MIN <: bool) && (y =. mk_i128 (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let (result: i128), (overflowed: bool) = impl_16__overflowing_rem x y in
  if overflowed then Core_models.Panicking.Internal.panic #i128 () else result

/// See [`std::primitive::i8::div_euclid`] (and similar for other signed integer types)
let impl_16__div_euclid (x y: i128)
    : Prims.Pure i128
      (requires y <>. mk_i128 0 && ~.((x =. impl_16__MIN <: bool) && (y =. mk_i128 (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let q:i128 = x /! y in
  if (x %! y <: i128) <. mk_i128 0
  then
    if y >. mk_i128 0
    then impl_16__wrapping_sub q (mk_i128 1)
    else impl_16__wrapping_add q (mk_i128 1)
  else q

/// See [`std::primitive::i8::overflowing_div_euclid`] (and similar for other signed integer types)
let impl_16__overflowing_div_euclid (x y: i128)
    : Prims.Pure (i128 & bool) (requires y <>. mk_i128 0) (fun _ -> Prims.l_True) =
  if x =. impl_16__MIN && y =. mk_i128 (-1)
  then x, true <: (i128 & bool)
  else impl_16__div_euclid x y, false <: (i128 & bool)

/// See [`std::primitive::i8::wrapping_div_euclid`] (and similar for other signed integer types)
let impl_16__wrapping_div_euclid (x y: i128)
    : Prims.Pure i128 (requires y <>. mk_i128 0) (fun _ -> Prims.l_True) =
  let (result: i128), (_: bool) = impl_16__overflowing_div_euclid x y in
  result

/// See [`std::primitive::i8::strict_div_euclid`] (and similar for other signed integer types)
let impl_16__strict_div_euclid (x y: i128)
    : Prims.Pure i128
      (requires y <>. mk_i128 0 && ~.((x =. impl_16__MIN <: bool) && (y =. mk_i128 (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let (result: i128), (overflowed: bool) = impl_16__overflowing_div_euclid x y in
  if overflowed then Core_models.Panicking.Internal.panic #i128 () else result

/// See [`std::primitive::i8::overflowing_rem_euclid`] (and similar for other signed integer types)
let impl_16__overflowing_rem_euclid (x y: i128)
    : Prims.Pure (i128 & bool) (requires y <>. mk_i128 0) (fun _ -> Prims.l_True) =
  if y =. mk_i128 (-1)
  then mk_i128 0, x =. impl_16__MIN <: (i128 & bool)
  else impl_16__rem_euclid x y, false <: (i128 & bool)

/// See [`std::primitive::i8::wrapping_rem_euclid`] (and similar for other signed integer types)
let impl_16__wrapping_rem_euclid (x y: i128)
    : Prims.Pure i128 (requires y <>. mk_i128 0) (fun _ -> Prims.l_True) =
  let (result: i128), (_: bool) = impl_16__overflowing_rem_euclid x y in
  result

/// See [`std::primitive::i8::strict_rem_euclid`] (and similar for other signed integer types)
let impl_16__strict_rem_euclid (x y: i128)
    : Prims.Pure i128
      (requires y <>. mk_i128 0 && ~.((x =. impl_16__MIN <: bool) && (y =. mk_i128 (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let (result: i128), (overflowed: bool) = impl_16__overflowing_rem_euclid x y in
  if overflowed then Core_models.Panicking.Internal.panic #i128 () else result

/// See [`std::primitive::i8::div_floor`] (and similar for other signed integer types)
let impl_16__div_floor (x y: i128)
    : Prims.Pure i128
      (requires y <>. mk_i128 0 && ~.((x =. impl_16__MIN <: bool) && (y =. mk_i128 (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let d:i128 = x /! y in
  let r:i128 = x %! y in
  if r <>. mk_i128 0 && (x <. mk_i128 0 <: bool) <>. (y <. mk_i128 0 <: bool)
  then impl_16__wrapping_sub d (mk_i128 1)
  else d

/// See [`std::primitive::i8::unchecked_div_exact`] (and similar for other signed integer types)
let impl_16__unchecked_div_exact (x y: i128)
    : Prims.Pure i128
      (requires y >. mk_i128 0 && (x %! y <: i128) =. mk_i128 0)
      (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::i8::strict_add_unsigned`] (and similar for other signed integer types)
let impl_16__strict_add_unsigned (x: i128) (y: u128)
    : Prims.Pure i128
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_16__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: i128), (overflowed: bool) = impl_16__overflowing_add_unsigned x y in
  if overflowed then Core_models.Panicking.Internal.panic #i128 () else result

/// See [`std::primitive::i8::strict_sub_unsigned`] (and similar for other signed integer types)
let impl_16__strict_sub_unsigned (x: i128) (y: u128)
    : Prims.Pure i128
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_16__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: i128), (overflowed: bool) = impl_16__overflowing_sub_unsigned x y in
  if overflowed then Core_models.Panicking.Internal.panic #i128 () else result

/// See [`std::primitive::i8::strict_shl`] (and similar for other integer types)
let impl_16__strict_shl (x: i128) (n: u32)
    : Prims.Pure i128 (requires n <. impl_16__BITS) (fun _ -> Prims.l_True) =
  if n <. impl_16__BITS then x <<! n else Core_models.Panicking.Internal.panic #i128 ()

/// See [`std::primitive::i8::strict_shr`] (and similar for other integer types)
let impl_16__strict_shr (x: i128) (n: u32)
    : Prims.Pure i128 (requires n <. impl_16__BITS) (fun _ -> Prims.l_True) =
  if n <. impl_16__BITS then x >>! n else Core_models.Panicking.Internal.panic #i128 ()

/// See [`std::primitive::i8::unchecked_shl`] (and similar for other integer types)
let impl_16__unchecked_shl (x: i128) (n: u32)
    : Prims.Pure i128 (requires n <. impl_16__BITS) (fun _ -> Prims.l_True) = x <<! n

/// See [`std::primitive::i8::unchecked_shr`] (and similar for other integer types)
let impl_16__unchecked_shr (x: i128) (n: u32)
    : Prims.Pure i128 (requires n <. impl_16__BITS) (fun _ -> Prims.l_True) = x >>! n

/// See [`std::primitive::i8::unchecked_shl_exact`] (and similar for other signed integer types)
let impl_16__unchecked_shl_exact (x: i128) (n: u32)
    : Prims.Pure i128
      (requires
        (n <. (impl_16__leading_zeros x <: u32) || n <. (impl_16__leading_ones x <: u32)) &&
        n <. impl_16__BITS)
      (fun _ -> Prims.l_True) = x <<! n

/// See [`std::primitive::i8::unchecked_shr_exact`] (and similar for other integer types)
let impl_16__unchecked_shr_exact (x: i128) (n: u32)
    : Prims.Pure i128
      (requires n <=. (impl_16__trailing_zeros x <: u32) && n <. impl_16__BITS)
      (fun _ -> Prims.l_True) = x >>! n

/// See [`std::primitive::i8::MIN`] (and similar for other signed integer types)
let impl_17__MIN: isize = Rust_primitives.Arithmetic.v_ISIZE_MIN

/// See [`std::primitive::i8::MAX`] (and similar for other signed integer types)
let impl_17__MAX: isize = Rust_primitives.Arithmetic.v_ISIZE_MAX

/// See [`std::primitive::i8::BITS`] (and similar for other signed integer types)
let impl_17__BITS: u32 = Rust_primitives.Arithmetic.v_SIZE_BITS

let impl_17__wrapping_add (x y: isize) : isize = Rust_primitives.Arithmetic.wrapping_add_isize x y

/// See [`std::primitive::u8::saturating_add`] (and similar for other integer types)
let impl_17__saturating_add (x y: isize) : isize =
  Rust_primitives.Arithmetic.saturating_add_isize x y

/// See [`std::primitive::u8::overflowing_add`] (and similar for other integer types)
let impl_17__overflowing_add (x y: isize) : (isize & bool) =
  Rust_primitives.Arithmetic.overflowing_add_isize x y

/// See [`std::primitive::u8::wrapping_sub`] (and similar for other integer types)
let impl_17__wrapping_sub (x y: isize) : isize = Rust_primitives.Arithmetic.wrapping_sub_isize x y

/// See [`std::primitive::u8::saturating_sub`] (and similar for other integer types)
let impl_17__saturating_sub (x y: isize) : isize =
  Rust_primitives.Arithmetic.saturating_sub_isize x y

/// See [`std::primitive::u8::overflowing_sub`] (and similar for other integer types)
let impl_17__overflowing_sub (x y: isize) : (isize & bool) =
  Rust_primitives.Arithmetic.overflowing_sub_isize x y

/// See [`std::primitive::u8::wrapping_mul`] (and similar for other integer types)
let impl_17__wrapping_mul (x y: isize) : isize = Rust_primitives.Arithmetic.wrapping_mul_isize x y

/// See [`std::primitive::u8::saturating_mul`] (and similar for other integer types)
let impl_17__saturating_mul (x y: isize) : isize =
  Rust_primitives.Arithmetic.saturating_mul_isize x y

/// See [`std::primitive::u8::overflowing_mul`] (and similar for other integer types)
let impl_17__overflowing_mul (x y: isize) : (isize & bool) =
  Rust_primitives.Arithmetic.overflowing_mul_isize x y

/// See [`std::primitive::u8::pow`] (and similar for other integer types)
let impl_17__pow (x: isize) (exp: u32) : isize = Rust_primitives.Arithmetic.pow_isize x exp

/// See [`std::primitive::u8::overflowing_pow`] (and similar for other integer types)
let impl_17__overflowing_pow (x: isize) (exp: u32) : (isize & bool) =
  Rust_primitives.Arithmetic.overflowing_pow_isize x exp

/// See [`std::primitive::u8::count_ones`] (and similar for other integer types)
let impl_17__count_ones (x: isize) : u32 = Rust_primitives.Arithmetic.count_ones_isize x

/// See [`std::primitive::u8::rotate_right`] (and similar for other integer types)
assume
val impl_17__rotate_right': x: isize -> n: u32 -> isize

unfold
let impl_17__rotate_right = impl_17__rotate_right'

/// See [`std::primitive::u8::rotate_left`] (and similar for other integer types)
assume
val impl_17__rotate_left': x: isize -> n: u32 -> isize

unfold
let impl_17__rotate_left = impl_17__rotate_left'

/// See [`std::primitive::u8::leading_zeros`] (and similar for other integer types)
assume
val impl_17__leading_zeros': x: isize -> u32

unfold
let impl_17__leading_zeros = impl_17__leading_zeros'

/// See [`std::primitive::u8::ilog2`] (and similar for other integer types)
assume
val impl_17__ilog2': x: isize -> u32

unfold
let impl_17__ilog2 = impl_17__ilog2'

/// See [`std::primitive::u8::from_be_bytes`] (and similar for other integer types)
assume
val impl_17__from_be_bytes': bytes: t_Array u8 (mk_usize 8) -> isize

unfold
let impl_17__from_be_bytes = impl_17__from_be_bytes'

/// See [`std::primitive::u8::from_le_bytes`] (and similar for other integer types)
assume
val impl_17__from_le_bytes': bytes: t_Array u8 (mk_usize 8) -> isize

unfold
let impl_17__from_le_bytes = impl_17__from_le_bytes'

/// See [`std::primitive::u8::to_be_bytes`] (and similar for other integer types)
assume
val impl_17__to_be_bytes': bytes: isize -> t_Array u8 (mk_usize 8)

unfold
let impl_17__to_be_bytes = impl_17__to_be_bytes'

/// See [`std::primitive::u8::to_le_bytes`] (and similar for other integer types)
assume
val impl_17__to_le_bytes': bytes: isize -> t_Array u8 (mk_usize 8)

unfold
let impl_17__to_le_bytes = impl_17__to_le_bytes'

/// See [`std::primitive::i8::signum`] (and similar for other signed integer types)
let impl_17__signum (x: isize) : isize =
  if x >. mk_isize 0 then mk_isize 1 else if x =. mk_isize 0 then mk_isize 0 else mk_isize (-1)

/// See [`std::primitive::i8::wrapping_neg`] (and similar for other signed integer types)
let impl_17__wrapping_neg (x: isize) : isize =
  Rust_primitives.Arithmetic.wrapping_sub_isize (mk_isize 0) x

/// See [`std::primitive::i8::min_value`] (and similar for other integer types)
let impl_17__min_value (_: Prims.unit) : isize = impl_17__MIN

/// See [`std::primitive::i8::max_value`] (and similar for other integer types)
let impl_17__max_value (_: Prims.unit) : isize = impl_17__MAX

/// See [`std::primitive::i8::cast_unsigned`] (and similar for other signed integer types)
let impl_17__cast_unsigned (x: isize) : usize = cast (x <: isize) <: usize

/// See [`std::primitive::i8::is_positive`] (and similar for other signed integer types)
let impl_17__is_positive (x: isize) : bool = x >. mk_isize 0

/// See [`std::primitive::i8::is_negative`] (and similar for other signed integer types)
let impl_17__is_negative (x: isize) : bool = x <. mk_isize 0

/// See [`std::primitive::i8::count_zeros`] (and similar for other integer types)
let impl_17__count_zeros (x: isize) : u32 = impl_17__BITS -! (impl_17__count_ones x <: u32)

/// See [`std::primitive::i8::overflowing_neg`] (and similar for other integer types)
let impl_17__overflowing_neg (x: isize) : (isize & bool) =
  if x =. impl_17__MIN
  then impl_17__MIN, true <: (isize & bool)
  else impl_17__wrapping_neg x, false <: (isize & bool)

/// See [`std::primitive::i8::saturating_neg`] (and similar for other signed integer types)
let impl_17__saturating_neg (x: isize) : isize =
  if x =. impl_17__MIN then impl_17__MAX else impl_17__wrapping_neg x

/// See [`std::primitive::i8::wrapping_abs`] (and similar for other signed integer types)
let impl_17__wrapping_abs (x: isize) : isize =
  if x <. mk_isize 0 then impl_17__wrapping_neg x else x

/// See [`std::primitive::i8::overflowing_abs`] (and similar for other signed integer types)
let impl_17__overflowing_abs (x: isize) : (isize & bool) =
  impl_17__wrapping_abs x, x =. impl_17__MIN <: (isize & bool)

/// See [`std::primitive::i8::saturating_abs`] (and similar for other signed integer types)
let impl_17__saturating_abs (x: isize) : isize =
  if x <. mk_isize 0 then impl_17__saturating_neg x else x

/// See [`std::primitive::i8::unsigned_abs`] (and similar for other signed integer types)
let impl_17__unsigned_abs (x: isize) : usize = cast (impl_17__wrapping_abs x <: isize) <: usize

/// See [`std::primitive::i8::wrapping_pow`] (and similar for other integer types)
let impl_17__wrapping_pow (x: isize) (exp: u32) : isize =
  let (result: isize), (_: bool) = impl_17__overflowing_pow x exp in
  result

/// See [`std::primitive::i8::saturating_pow`] (and similar for other signed integer types)
let impl_17__saturating_pow (x: isize) (exp: u32) : isize =
  let (result: isize), (overflowed: bool) = impl_17__overflowing_pow x exp in
  if ~.overflowed
  then result
  else
    if x <. mk_isize 0 && (exp %! mk_u32 2 <: u32) =. mk_u32 1 then impl_17__MIN else impl_17__MAX

/// See [`std::primitive::i8::abs_diff`] (and similar for other signed integer types)
let impl_17__abs_diff (x y: isize) : usize =
  if x <. y
  then cast (impl_17__wrapping_sub y x <: isize) <: usize
  else cast (impl_17__wrapping_sub x y <: isize) <: usize

/// See [`std::primitive::i8::midpoint`] (and similar for other signed integer types)
let impl_17__midpoint (x y: isize) : isize =
  let d:isize = x ^. y in
  let t:isize = impl_17__wrapping_add (d >>! mk_i32 1 <: isize) (x &. y <: isize) in
  if t <. mk_isize 0 then impl_17__wrapping_add t (d &. mk_isize 1 <: isize) else t

/// See [`std::primitive::i8::wrapping_add_unsigned`] (and similar for other signed integer types)
let impl_17__wrapping_add_unsigned (x: isize) (y: usize) : isize =
  impl_17__wrapping_add x (cast (y <: usize) <: isize)

/// See [`std::primitive::i8::wrapping_sub_unsigned`] (and similar for other signed integer types)
let impl_17__wrapping_sub_unsigned (x: isize) (y: usize) : isize =
  impl_17__wrapping_sub x (cast (y <: usize) <: isize)

/// See [`std::primitive::i8::overflowing_add_unsigned`] (and similar for other signed integer types)
let impl_17__overflowing_add_unsigned (x: isize) (y: usize) : (isize & bool) =
  let rhs:isize = cast (y <: usize) <: isize in
  let (result: isize), (overflowed: bool) = impl_17__overflowing_add x rhs in
  result, overflowed <>. (rhs <. mk_isize 0 <: bool) <: (isize & bool)

/// See [`std::primitive::i8::overflowing_sub_unsigned`] (and similar for other signed integer types)
let impl_17__overflowing_sub_unsigned (x: isize) (y: usize) : (isize & bool) =
  let rhs:isize = cast (y <: usize) <: isize in
  let (result: isize), (overflowed: bool) = impl_17__overflowing_sub x rhs in
  result, overflowed <>. (rhs <. mk_isize 0 <: bool) <: (isize & bool)

/// See [`std::primitive::i8::saturating_add_unsigned`] (and similar for other signed integer types)
let impl_17__saturating_add_unsigned (x: isize) (y: usize) : isize =
  let (result: isize), (overflowed: bool) = impl_17__overflowing_add_unsigned x y in
  if overflowed then impl_17__MAX else result

/// See [`std::primitive::i8::saturating_sub_unsigned`] (and similar for other signed integer types)
let impl_17__saturating_sub_unsigned (x: isize) (y: usize) : isize =
  let (result: isize), (overflowed: bool) = impl_17__overflowing_sub_unsigned x y in
  if overflowed then impl_17__MIN else result

/// See [`std::primitive::i8::reverse_bits`] (and similar for other signed integer types)
let impl_17__reverse_bits (x: isize) : isize =
  cast (impl_11__reverse_bits (cast (x <: isize) <: usize) <: usize) <: isize

/// See [`std::primitive::i8::widening_mul`] (and similar for other signed integer types)
let impl_17__widening_mul (x y: isize) : (usize & isize) =
  let (low: usize), (high: usize) =
    impl_11__widening_mul (cast (x <: isize) <: usize) (cast (y <: isize) <: usize)
  in
  let high:isize = cast (high <: usize) <: isize in
  let high:isize = if x <. mk_isize 0 then impl_17__wrapping_sub high y else high in
  let high:isize = if y <. mk_isize 0 then impl_17__wrapping_sub high x else high in
  low, high <: (usize & isize)

/// See [`std::primitive::i8::carrying_mul_add`] (and similar for other signed integer types)
let impl_17__carrying_mul_add (x y carry add: isize) : (usize & isize) =
  let (low: usize), (high: isize) = impl_17__widening_mul x y in
  let (low: usize), (c1: bool) = impl_11__overflowing_add low (cast (carry <: isize) <: usize) in
  let (low: usize), (c2: bool) = impl_11__overflowing_add low (cast (add <: isize) <: usize) in
  let high:isize = impl_17__wrapping_add high (if c1 then mk_isize 1 else mk_isize 0) in
  let high:isize = impl_17__wrapping_add high (if c2 then mk_isize 1 else mk_isize 0) in
  let high:isize =
    impl_17__wrapping_add high (if carry <. mk_isize 0 <: bool then mk_isize (-1) else mk_isize 0)
  in
  let high:isize =
    impl_17__wrapping_add high (if add <. mk_isize 0 <: bool then mk_isize (-1) else mk_isize 0)
  in
  low, high <: (usize & isize)

/// See [`std::primitive::i8::carrying_mul`] (and similar for other signed integer types)
let impl_17__carrying_mul (x y carry: isize) : (usize & isize) =
  impl_17__carrying_mul_add x y carry (mk_isize 0)

/// See [`std::primitive::i8::carrying_add`] (and similar for other integer types)
let impl_17__carrying_add (x y: isize) (carry: bool) : (isize & bool) =
  let (a: isize), (b: bool) = impl_17__overflowing_add x y in
  let (c: isize), (d: bool) =
    impl_17__overflowing_add a (if carry then mk_isize 1 else mk_isize 0)
  in
  c, b <>. d <: (isize & bool)

/// See [`std::primitive::i8::borrowing_sub`] (and similar for other integer types)
let impl_17__borrowing_sub (x y: isize) (borrow: bool) : (isize & bool) =
  let (a: isize), (b: bool) = impl_17__overflowing_sub x y in
  let (c: isize), (d: bool) =
    impl_17__overflowing_sub a (if borrow then mk_isize 1 else mk_isize 0)
  in
  c, b <>. d <: (isize & bool)

/// See [`std::primitive::i8::trailing_zeros`] (and similar for other integer types)
let impl_17__trailing_zeros (x: isize) : u32 =
  if x =. mk_isize 0
  then impl_17__BITS
  else
    impl_17__count_ones (impl_17__wrapping_sub (x &. (impl_17__wrapping_neg x <: isize) <: isize)
          (mk_isize 1)
        <:
        isize)

/// See [`std::primitive::i8::trailing_ones`] (and similar for other integer types)
let impl_17__trailing_ones (x: isize) : u32 =
  impl_17__trailing_zeros (impl_17__wrapping_sub (mk_isize (-1)) x <: isize)

/// See [`std::primitive::i8::leading_ones`] (and similar for other integer types)
let impl_17__leading_ones (x: isize) : u32 =
  impl_17__leading_zeros (impl_17__wrapping_sub (mk_isize (-1)) x <: isize)

/// See [`std::primitive::i8::isolate_lowest_one`] (and similar for other integer types)
let impl_17__isolate_lowest_one (x: isize) : isize = x &. (impl_17__wrapping_neg x <: isize)

/// See [`std::primitive::i8::swap_bytes`] (and similar for other integer types)
let impl_17__swap_bytes (x: isize) : isize =
  impl_17__from_le_bytes (impl_17__to_be_bytes x <: t_Array u8 (mk_usize 8))

/// See [`std::primitive::i8::to_be`] (and similar for other integer types)
let impl_17__to_be (x: isize) : isize = impl_17__swap_bytes x

/// See [`std::primitive::i8::to_le`] (and similar for other integer types)
let impl_17__to_le (x: isize) : isize = x

/// See [`std::primitive::i8::from_be`] (and similar for other integer types)
let impl_17__from_be (x: isize) : isize = impl_17__swap_bytes x

/// See [`std::primitive::i8::from_le`] (and similar for other integer types)
let impl_17__from_le (x: isize) : isize = x

/// See [`std::primitive::i8::to_ne_bytes`] (and similar for other integer types)
let impl_17__to_ne_bytes (x: isize) : t_Array u8 (mk_usize 8) = impl_17__to_le_bytes x

/// See [`std::primitive::i8::from_ne_bytes`] (and similar for other integer types)
let impl_17__from_ne_bytes (bytes: t_Array u8 (mk_usize 8)) : isize = impl_17__from_le_bytes bytes

/// See [`std::primitive::i8::wrapping_shl`] (and similar for other integer types)
let impl_17__wrapping_shl (x: isize) (n: u32) : isize = x <<! (n %! impl_17__BITS <: u32)

/// See [`std::primitive::i8::wrapping_shr`] (and similar for other integer types)
let impl_17__wrapping_shr (x: isize) (n: u32) : isize = x >>! (n %! impl_17__BITS <: u32)

/// See [`std::primitive::i8::isolate_highest_one`] (and similar for other integer types)
let impl_17__isolate_highest_one (x: isize) : isize =
  x &. (impl_17__wrapping_shr impl_17__MIN (impl_17__leading_zeros x <: u32) <: isize)

/// See [`std::primitive::i8::overflowing_shl`] (and similar for other integer types)
let impl_17__overflowing_shl (x: isize) (n: u32) : (isize & bool) =
  impl_17__wrapping_shl x n, n >=. impl_17__BITS <: (isize & bool)

/// See [`std::primitive::i8::overflowing_shr`] (and similar for other integer types)
let impl_17__overflowing_shr (x: isize) (n: u32) : (isize & bool) =
  impl_17__wrapping_shr x n, n >=. impl_17__BITS <: (isize & bool)

/// See [`std::primitive::i8::unbounded_shl`] (and similar for other integer types)
let impl_17__unbounded_shl (x: isize) (n: u32) : isize =
  if n <. impl_17__BITS then x <<! n else mk_isize 0

/// See [`std::primitive::i8::unbounded_shr`] (and similar for other signed integer types)
let impl_17__unbounded_shr (x: isize) (n: u32) : isize =
  if n <. impl_17__BITS then x >>! n else x >>! (impl_17__BITS -! mk_u32 1 <: u32)

/// See [`std::primitive::i8::clamp_magnitude`] (and similar for other signed integer types)
let impl_17__clamp_magnitude (x: isize) (limit: usize) : isize =
  if limit >. (cast (impl_17__MAX <: isize) <: usize)
  then x
  else
    let hi:isize = cast (limit <: usize) <: isize in
    let lo:isize = impl_17__wrapping_neg hi in
    if x <. lo then lo else if x >. hi then hi else x

/// See [`std::primitive::u8::unchecked_add`] (and similar for other integer types)
let impl_17__unchecked_add (x y: isize)
    : Prims.Pure isize
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_17__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_17__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) = x +! y

/// See [`std::primitive::u8::unchecked_sub`] (and similar for other integer types)
let impl_17__unchecked_sub (x y: isize)
    : Prims.Pure isize
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_17__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_17__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) = x -! y

/// See [`std::primitive::u8::unchecked_mul`] (and similar for other integer types)
let impl_17__unchecked_mul (x y: isize)
    : Prims.Pure isize
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_17__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_17__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) = x *! y

/// See [`std::primitive::u8::rem_euclid`] (and similar for other integer types)
let impl_17__rem_euclid (x y: isize)
    : Prims.Pure isize
      (requires y <>. mk_isize 0 && ~.((x =. impl_17__MIN <: bool) && (y =. mk_isize (-1) <: bool)))
      (fun _ -> Prims.l_True) = Rust_primitives.Arithmetic.rem_euclid_isize x y

/// See [`std::primitive::i8::abs`] (and similar for other signed integer types)
let impl_17__abs (x: isize) : Prims.Pure isize (requires x >. impl_17__MIN) (fun _ -> Prims.l_True) =
  Rust_primitives.Arithmetic.abs_isize x

/// See [`std::primitive::u8::unchecked_div`] (and similar for other integer types)
let impl_17__unchecked_div (x y: isize)
    : Prims.Pure isize
      (requires y <>. mk_isize 0 && (x <>. impl_17__MIN || y <>. mk_isize (-1)))
      (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::u8::unchecked_rem`] (and similar for other integer types)
let impl_17__unchecked_rem (x y: isize)
    : Prims.Pure isize
      (requires y <>. mk_isize 0 && (x <>. impl_17__MIN || y <>. mk_isize (-1)))
      (fun _ -> Prims.l_True) = x %! y

/// See [`std::primitive::i8::div_ceil`] (and similar for other signed integer types)
let impl_17__div_ceil (x y: isize)
    : Prims.Pure isize
      (requires y <>. mk_isize 0 && ~.((x =. impl_17__MIN <: bool) && (y =. mk_isize (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let d:isize = x /! y in
  let r:isize = x %! y in
  if r >. mk_isize 0 && y >. mk_isize 0 || r <. mk_isize 0 && y <. mk_isize 0
  then d +! mk_isize 1
  else d

/// See [`std::primitive::i8::strict_neg`] (and similar for other integer types)
let impl_17__strict_neg (x: isize)
    : Prims.Pure isize (requires x <>. impl_17__MIN) (fun _ -> Prims.l_True) =
  if x =. impl_17__MIN
  then Core_models.Panicking.Internal.panic #isize ()
  else impl_17__wrapping_neg x

/// See [`std::primitive::i8::unchecked_neg`] (and similar for other signed integer types)
let impl_17__unchecked_neg (x: isize)
    : Prims.Pure isize (requires x <>. impl_17__MIN) (fun _ -> Prims.l_True) = mk_isize 0 -! x

/// See [`std::primitive::i8::strict_abs`] (and similar for other signed integer types)
let impl_17__strict_abs (x: isize)
    : Prims.Pure isize (requires x <>. impl_17__MIN) (fun _ -> Prims.l_True) =
  if x <. mk_isize 0 then impl_17__strict_neg x else x

/// See [`std::primitive::i8::strict_pow`] (and similar for other integer types)
let impl_17__strict_pow (x: isize) (exp: u32)
    : Prims.Pure isize
      (requires (impl_17__overflowing_pow x exp <: (isize & bool))._2 =. false)
      (fun _ -> Prims.l_True) =
  let (result: isize), (overflowed: bool) = impl_17__overflowing_pow x exp in
  if overflowed then Core_models.Panicking.Internal.panic #isize () else result

/// See [`std::primitive::i8::strict_add`] (and similar for other integer types)
let impl_17__strict_add (x y: isize)
    : Prims.Pure isize
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_17__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_17__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: isize), (overflowed: bool) = impl_17__overflowing_add x y in
  if overflowed then Core_models.Panicking.Internal.panic #isize () else result

/// See [`std::primitive::i8::strict_sub`] (and similar for other integer types)
let impl_17__strict_sub (x y: isize)
    : Prims.Pure isize
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_17__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_17__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: isize), (overflowed: bool) = impl_17__overflowing_sub x y in
  if overflowed then Core_models.Panicking.Internal.panic #isize () else result

/// See [`std::primitive::i8::strict_mul`] (and similar for other integer types)
let impl_17__strict_mul (x y: isize)
    : Prims.Pure isize
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_17__MAX <: Hax_lib.Int.t_Int) &&
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) *
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_17__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: isize), (overflowed: bool) = impl_17__overflowing_mul x y in
  if overflowed then Core_models.Panicking.Internal.panic #isize () else result

/// See [`std::primitive::i8::overflowing_div`] (and similar for other signed integer types)
let impl_17__overflowing_div (x y: isize)
    : Prims.Pure (isize & bool) (requires y <>. mk_isize 0) (fun _ -> Prims.l_True) =
  if x =. impl_17__MIN && y =. mk_isize (-1)
  then x, true <: (isize & bool)
  else x /! y, false <: (isize & bool)

/// See [`std::primitive::i8::overflowing_rem`] (and similar for other signed integer types)
let impl_17__overflowing_rem (x y: isize)
    : Prims.Pure (isize & bool) (requires y <>. mk_isize 0) (fun _ -> Prims.l_True) =
  if y =. mk_isize (-1)
  then mk_isize 0, x =. impl_17__MIN <: (isize & bool)
  else x %! y, false <: (isize & bool)

/// See [`std::primitive::i8::wrapping_div`] (and similar for other signed integer types)
let impl_17__wrapping_div (x y: isize)
    : Prims.Pure isize (requires y <>. mk_isize 0) (fun _ -> Prims.l_True) =
  let (result: isize), (_: bool) = impl_17__overflowing_div x y in
  result

/// See [`std::primitive::i8::wrapping_rem`] (and similar for other signed integer types)
let impl_17__wrapping_rem (x y: isize)
    : Prims.Pure isize (requires y <>. mk_isize 0) (fun _ -> Prims.l_True) =
  let (result: isize), (_: bool) = impl_17__overflowing_rem x y in
  result

/// See [`std::primitive::i8::saturating_div`] (and similar for other signed integer types)
let impl_17__saturating_div (x y: isize)
    : Prims.Pure isize (requires y <>. mk_isize 0) (fun _ -> Prims.l_True) =
  let (result: isize), (overflowed: bool) = impl_17__overflowing_div x y in
  if overflowed then impl_17__MAX else result

/// See [`std::primitive::i8::strict_div`] (and similar for other signed integer types)
let impl_17__strict_div (x y: isize)
    : Prims.Pure isize
      (requires y <>. mk_isize 0 && ~.((x =. impl_17__MIN <: bool) && (y =. mk_isize (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let (result: isize), (overflowed: bool) = impl_17__overflowing_div x y in
  if overflowed then Core_models.Panicking.Internal.panic #isize () else result

/// See [`std::primitive::i8::strict_rem`] (and similar for other signed integer types)
let impl_17__strict_rem (x y: isize)
    : Prims.Pure isize
      (requires y <>. mk_isize 0 && ~.((x =. impl_17__MIN <: bool) && (y =. mk_isize (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let (result: isize), (overflowed: bool) = impl_17__overflowing_rem x y in
  if overflowed then Core_models.Panicking.Internal.panic #isize () else result

/// See [`std::primitive::i8::div_euclid`] (and similar for other signed integer types)
let impl_17__div_euclid (x y: isize)
    : Prims.Pure isize
      (requires y <>. mk_isize 0 && ~.((x =. impl_17__MIN <: bool) && (y =. mk_isize (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let q:isize = x /! y in
  if (x %! y <: isize) <. mk_isize 0
  then
    if y >. mk_isize 0
    then impl_17__wrapping_sub q (mk_isize 1)
    else impl_17__wrapping_add q (mk_isize 1)
  else q

/// See [`std::primitive::i8::overflowing_div_euclid`] (and similar for other signed integer types)
let impl_17__overflowing_div_euclid (x y: isize)
    : Prims.Pure (isize & bool) (requires y <>. mk_isize 0) (fun _ -> Prims.l_True) =
  if x =. impl_17__MIN && y =. mk_isize (-1)
  then x, true <: (isize & bool)
  else impl_17__div_euclid x y, false <: (isize & bool)

/// See [`std::primitive::i8::wrapping_div_euclid`] (and similar for other signed integer types)
let impl_17__wrapping_div_euclid (x y: isize)
    : Prims.Pure isize (requires y <>. mk_isize 0) (fun _ -> Prims.l_True) =
  let (result: isize), (_: bool) = impl_17__overflowing_div_euclid x y in
  result

/// See [`std::primitive::i8::strict_div_euclid`] (and similar for other signed integer types)
let impl_17__strict_div_euclid (x y: isize)
    : Prims.Pure isize
      (requires y <>. mk_isize 0 && ~.((x =. impl_17__MIN <: bool) && (y =. mk_isize (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let (result: isize), (overflowed: bool) = impl_17__overflowing_div_euclid x y in
  if overflowed then Core_models.Panicking.Internal.panic #isize () else result

/// See [`std::primitive::i8::overflowing_rem_euclid`] (and similar for other signed integer types)
let impl_17__overflowing_rem_euclid (x y: isize)
    : Prims.Pure (isize & bool) (requires y <>. mk_isize 0) (fun _ -> Prims.l_True) =
  if y =. mk_isize (-1)
  then mk_isize 0, x =. impl_17__MIN <: (isize & bool)
  else impl_17__rem_euclid x y, false <: (isize & bool)

/// See [`std::primitive::i8::wrapping_rem_euclid`] (and similar for other signed integer types)
let impl_17__wrapping_rem_euclid (x y: isize)
    : Prims.Pure isize (requires y <>. mk_isize 0) (fun _ -> Prims.l_True) =
  let (result: isize), (_: bool) = impl_17__overflowing_rem_euclid x y in
  result

/// See [`std::primitive::i8::strict_rem_euclid`] (and similar for other signed integer types)
let impl_17__strict_rem_euclid (x y: isize)
    : Prims.Pure isize
      (requires y <>. mk_isize 0 && ~.((x =. impl_17__MIN <: bool) && (y =. mk_isize (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let (result: isize), (overflowed: bool) = impl_17__overflowing_rem_euclid x y in
  if overflowed then Core_models.Panicking.Internal.panic #isize () else result

/// See [`std::primitive::i8::div_floor`] (and similar for other signed integer types)
let impl_17__div_floor (x y: isize)
    : Prims.Pure isize
      (requires y <>. mk_isize 0 && ~.((x =. impl_17__MIN <: bool) && (y =. mk_isize (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  let d:isize = x /! y in
  let r:isize = x %! y in
  if r <>. mk_isize 0 && (x <. mk_isize 0 <: bool) <>. (y <. mk_isize 0 <: bool)
  then impl_17__wrapping_sub d (mk_isize 1)
  else d

/// See [`std::primitive::i8::unchecked_div_exact`] (and similar for other signed integer types)
let impl_17__unchecked_div_exact (x y: isize)
    : Prims.Pure isize
      (requires y >. mk_isize 0 && (x %! y <: isize) =. mk_isize 0)
      (fun _ -> Prims.l_True) = x /! y

/// See [`std::primitive::i8::strict_add_unsigned`] (and similar for other signed integer types)
let impl_17__strict_add_unsigned (x: isize) (y: usize)
    : Prims.Pure isize
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine impl_17__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: isize), (overflowed: bool) = impl_17__overflowing_add_unsigned x y in
  if overflowed then Core_models.Panicking.Internal.panic #isize () else result

/// See [`std::primitive::i8::strict_sub_unsigned`] (and similar for other signed integer types)
let impl_17__strict_sub_unsigned (x: isize) (y: usize)
    : Prims.Pure isize
      (requires
        ((Rust_primitives.Hax.Int.from_machine x <: Hax_lib.Int.t_Int) -
          (Rust_primitives.Hax.Int.from_machine y <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) >=
        (Rust_primitives.Hax.Int.from_machine impl_17__MIN <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (result: isize), (overflowed: bool) = impl_17__overflowing_sub_unsigned x y in
  if overflowed then Core_models.Panicking.Internal.panic #isize () else result

/// See [`std::primitive::i8::strict_shl`] (and similar for other integer types)
let impl_17__strict_shl (x: isize) (n: u32)
    : Prims.Pure isize (requires n <. impl_17__BITS) (fun _ -> Prims.l_True) =
  if n <. impl_17__BITS then x <<! n else Core_models.Panicking.Internal.panic #isize ()

/// See [`std::primitive::i8::strict_shr`] (and similar for other integer types)
let impl_17__strict_shr (x: isize) (n: u32)
    : Prims.Pure isize (requires n <. impl_17__BITS) (fun _ -> Prims.l_True) =
  if n <. impl_17__BITS then x >>! n else Core_models.Panicking.Internal.panic #isize ()

/// See [`std::primitive::i8::unchecked_shl`] (and similar for other integer types)
let impl_17__unchecked_shl (x: isize) (n: u32)
    : Prims.Pure isize (requires n <. impl_17__BITS) (fun _ -> Prims.l_True) = x <<! n

/// See [`std::primitive::i8::unchecked_shr`] (and similar for other integer types)
let impl_17__unchecked_shr (x: isize) (n: u32)
    : Prims.Pure isize (requires n <. impl_17__BITS) (fun _ -> Prims.l_True) = x >>! n

/// See [`std::primitive::i8::unchecked_shl_exact`] (and similar for other signed integer types)
let impl_17__unchecked_shl_exact (x: isize) (n: u32)
    : Prims.Pure isize
      (requires
        (n <. (impl_17__leading_zeros x <: u32) || n <. (impl_17__leading_ones x <: u32)) &&
        n <. impl_17__BITS)
      (fun _ -> Prims.l_True) = x <<! n

/// See [`std::primitive::i8::unchecked_shr_exact`] (and similar for other integer types)
let impl_17__unchecked_shr_exact (x: isize) (n: u32)
    : Prims.Pure isize
      (requires n <=. (impl_17__trailing_zeros x <: u32) && n <. impl_17__BITS)
      (fun _ -> Prims.l_True) = x >>! n

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_18__from__num: Core_models.Default.t_Default u8 =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: u8) -> true);
    f_default = fun (_: Prims.unit) -> mk_u8 0
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_19__from__num: Core_models.Default.t_Default u16 =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: u16) -> true);
    f_default = fun (_: Prims.unit) -> mk_u16 0
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_20__from__num: Core_models.Default.t_Default u32 =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: u32) -> true);
    f_default = fun (_: Prims.unit) -> mk_u32 0
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_21__from__num: Core_models.Default.t_Default u64 =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: u64) -> true);
    f_default = fun (_: Prims.unit) -> mk_u64 0
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_22__from__num: Core_models.Default.t_Default u128 =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: u128) -> true);
    f_default = fun (_: Prims.unit) -> mk_u128 0
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_23__from__num: Core_models.Default.t_Default usize =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: usize) -> true);
    f_default = fun (_: Prims.unit) -> mk_usize 0
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_24__from__num: Core_models.Default.t_Default i8 =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: i8) -> true);
    f_default = fun (_: Prims.unit) -> mk_i8 0
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_25__from__num: Core_models.Default.t_Default i16 =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: i16) -> true);
    f_default = fun (_: Prims.unit) -> mk_i16 0
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_26__from__num: Core_models.Default.t_Default i32 =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: i32) -> true);
    f_default = fun (_: Prims.unit) -> mk_i32 0
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_27__from__num: Core_models.Default.t_Default i64 =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: i64) -> true);
    f_default = fun (_: Prims.unit) -> mk_i64 0
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_28__from__num: Core_models.Default.t_Default i128 =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: i128) -> true);
    f_default = fun (_: Prims.unit) -> mk_i128 0
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_29__from__num: Core_models.Default.t_Default isize =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: isize) -> true);
    f_default = fun (_: Prims.unit) -> mk_isize 0
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_30__from__num: Core_models.Default.t_Default bool =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: bool) -> true);
    f_default = fun (_: Prims.unit) -> false
  }

/// See [`std::ops::ControlFlow`]
type t_ControlFlow (v_B: Type0) (v_C: Type0) =
  | ControlFlow_Continue : v_C -> t_ControlFlow v_B v_C
  | ControlFlow_Break : v_B -> t_ControlFlow v_B v_C

/// See [`std::ops::ControlFlow::is_break`]
let impl__is_break (#v_B #v_C: Type0) (self: t_ControlFlow v_B v_C) : bool =
  match self <: t_ControlFlow v_B v_C with
  | ControlFlow_Break _ -> true
  | _ -> false

/// See [`std::ops::ControlFlow::is_continue`]
let impl__is_continue (#v_B #v_C: Type0) (self: t_ControlFlow v_B v_C) : bool =
  match self <: t_ControlFlow v_B v_C with
  | ControlFlow_Continue _ -> true
  | _ -> false

/// See [`std::ops::ControlFlow::map_break`]
let impl__map_break
      (#v_B #v_C #v_T #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_B)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_T})
      (self: t_ControlFlow v_B v_C)
      (f: v_F)
    : t_ControlFlow v_T v_C =
  match self <: t_ControlFlow v_B v_C with
  | ControlFlow_Continue x -> ControlFlow_Continue x <: t_ControlFlow v_T v_C
  | ControlFlow_Break x ->
    ControlFlow_Break
    (Core_models.Ops.Function.f_call_once #v_F #v_B #FStar.Tactics.Typeclasses.solve f (x <: v_B))
    <:
    t_ControlFlow v_T v_C

/// See [`std::ops::ControlFlow::map_continue`]
let impl__map_continue
      (#v_B #v_C #v_T #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_C)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_T})
      (self: t_ControlFlow v_B v_C)
      (f: v_F)
    : t_ControlFlow v_B v_T =
  match self <: t_ControlFlow v_B v_C with
  | ControlFlow_Continue x ->
    ControlFlow_Continue
    (Core_models.Ops.Function.f_call_once #v_F #v_C #FStar.Tactics.Typeclasses.solve f (x <: v_C))
    <:
    t_ControlFlow v_B v_T
  | ControlFlow_Break x -> ControlFlow_Break x <: t_ControlFlow v_B v_T

/// See [`std::ops::ControlFlow::into_value`]
let impl_1__into_value (#v_T: Type0) (self: t_ControlFlow v_T v_T) : v_T =
  match self <: t_ControlFlow v_T v_T with
  | ControlFlow_Continue x -> x
  | ControlFlow_Break x -> x

/// See [`std::ops::RangeTo`]
type t_RangeTo (v_T: Type0) = { f_end:v_T }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_27 (#v_T: Type0) (v_N: usize)
    : Core_models.Ops.Index.t_Index (t_Array v_T v_N) (t_RangeTo usize) =
  {
    f_Output = t_Slice v_T;
    f_index_pre = (fun (self_: t_Array v_T v_N) (i: t_RangeTo usize) -> i.f_end <=. v_N);
    f_index_post = (fun (self: t_Array v_T v_N) (i: t_RangeTo usize) (out: t_Slice v_T) -> true);
    f_index
    =
    fun (self: t_Array v_T v_N) (i: t_RangeTo usize) ->
      Rust_primitives.Slice.array_slice #v_T v_N self (mk_usize 0) i.f_end
  }

/// See [`std::ops::RangeFrom`]
type t_RangeFrom (v_T: Type0) = { f_start:v_T }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_28 (#v_T: Type0) (v_N: usize)
    : Core_models.Ops.Index.t_Index (t_Array v_T v_N) (t_RangeFrom usize) =
  {
    f_Output = t_Slice v_T;
    f_index_pre = (fun (self_: t_Array v_T v_N) (i: t_RangeFrom usize) -> i.f_start <=. v_N);
    f_index_post = (fun (self: t_Array v_T v_N) (i: t_RangeFrom usize) (out: t_Slice v_T) -> true);
    f_index
    =
    fun (self: t_Array v_T v_N) (i: t_RangeFrom usize) ->
      Rust_primitives.Slice.array_slice #v_T v_N self i.f_start v_N
  }

/// See [`std::ops::Range`]
type t_Range (v_T: Type0) = {
  f_start:v_T;
  f_end:v_T
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_26 (#v_T: Type0) (v_N: usize)
    : Core_models.Ops.Index.t_Index (t_Array v_T v_N) (t_Range usize) =
  {
    f_Output = t_Slice v_T;
    f_index_pre
    =
    (fun (self_: t_Array v_T v_N) (i: t_Range usize) -> i.f_start <=. i.f_end && i.f_end <=. v_N);
    f_index_post = (fun (self: t_Array v_T v_N) (i: t_Range usize) (out: t_Slice v_T) -> true);
    f_index
    =
    fun (self: t_Array v_T v_N) (i: t_Range usize) ->
      Rust_primitives.Slice.array_slice #v_T v_N self i.f_start i.f_end
  }

/// See [`std::ops::RangeFull`]
type t_RangeFull = | RangeFull : t_RangeFull

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_29 (#v_T: Type0) (v_N: usize) : Core_models.Ops.Index.t_Index (t_Array v_T v_N) t_RangeFull =
  {
    f_Output = t_Slice v_T;
    f_index_pre = (fun (self: t_Array v_T v_N) (i: t_RangeFull) -> true);
    f_index_post = (fun (self: t_Array v_T v_N) (i: t_RangeFull) (out: t_Slice v_T) -> true);
    f_index
    =
    fun (self: t_Array v_T v_N) (i: t_RangeFull) ->
      Rust_primitives.Slice.array_slice #v_T v_N self (mk_usize 0) v_N
  }

/// See [`std::ops::RangeInclusive`]
/// Real core also carries an `exhausted` flag, set once the range has been
/// iterated to its end, which makes a drained range report itself empty.
/// The model does not implement `Iterator` for `RangeInclusive`, so there
/// is nothing to observe it with; `is_empty`/`end_bound` below behave as if
/// the flag were always `false`.
type t_RangeInclusive (v_T: Type0) = {
  f_start:v_T;
  f_end:v_T
}

/// See [`std::ops::RangeToInclusive`]
type t_RangeToInclusive (v_T: Type0) = { f_end:v_T }

/// See [`std::ops::Bound`]
type t_Bound (v_T: Type0) =
  | Bound_Included : v_T -> t_Bound v_T
  | Bound_Excluded : v_T -> t_Bound v_T
  | Bound_Unbounded : t_Bound v_T

/// See [`std::ops::Bound::as_ref`]
let impl__as_ref (#v_T: Type0) (self: t_Bound v_T) : t_Bound v_T =
  match self <: t_Bound v_T with
  | Bound_Included x -> Bound_Included x <: t_Bound v_T
  | Bound_Excluded x -> Bound_Excluded x <: t_Bound v_T
  | Bound_Unbounded  -> Bound_Unbounded <: t_Bound v_T

/// See [`std::ops::Bound::map`]
let impl__map
      (#v_T #v_U #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_T)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_U})
      (self: t_Bound v_T)
      (f: v_F)
    : t_Bound v_U =
  match self <: t_Bound v_T with
  | Bound_Included x ->
    Bound_Included
    (Core_models.Ops.Function.f_call_once #v_F #v_T #FStar.Tactics.Typeclasses.solve f (x <: v_T))
    <:
    t_Bound v_U
  | Bound_Excluded x ->
    Bound_Excluded
    (Core_models.Ops.Function.f_call_once #v_F #v_T #FStar.Tactics.Typeclasses.solve f (x <: v_T))
    <:
    t_Bound v_U
  | Bound_Unbounded  -> Bound_Unbounded <: t_Bound v_U

/// See [`std::ops::Bound::cloned`]
let impl_1__cloned
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Clone.t_Clone v_T)
      (self: t_Bound v_T)
    : t_Bound v_T =
  match self <: t_Bound v_T with
  | Bound_Included x ->
    Bound_Included (Core_models.Clone.f_clone #v_T #FStar.Tactics.Typeclasses.solve x)
    <:
    t_Bound v_T
  | Bound_Excluded x ->
    Bound_Excluded (Core_models.Clone.f_clone #v_T #FStar.Tactics.Typeclasses.solve x)
    <:
    t_Bound v_T
  | Bound_Unbounded  -> Bound_Unbounded <: t_Bound v_T

/// See [`std::ops::Bound::copied`]
let impl_2__copied
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Marker.t_Copy v_T)
      (self: t_Bound v_T)
    : t_Bound v_T =
  match self <: t_Bound v_T with
  | Bound_Included x ->
    Bound_Included (Core_models.Clone.f_clone #v_T #FStar.Tactics.Typeclasses.solve x)
    <:
    t_Bound v_T
  | Bound_Excluded x ->
    Bound_Excluded (Core_models.Clone.f_clone #v_T #FStar.Tactics.Typeclasses.solve x)
    <:
    t_Bound v_T
  | Bound_Unbounded  -> Bound_Unbounded <: t_Bound v_T

/// See [`std::ops::OneSidedRangeBound`]
type t_OneSidedRangeBound =
  | OneSidedRangeBound_StartInclusive : t_OneSidedRangeBound
  | OneSidedRangeBound_End : t_OneSidedRangeBound
  | OneSidedRangeBound_EndInclusive : t_OneSidedRangeBound

let t_OneSidedRangeBound_cast_to_repr (x: t_OneSidedRangeBound) : isize =
  match x <: t_OneSidedRangeBound with
  | OneSidedRangeBound_StartInclusive  -> mk_isize 0
  | OneSidedRangeBound_End  -> mk_isize 1
  | OneSidedRangeBound_EndInclusive  -> mk_isize 2

/// See [`std::ops::RangeInclusive::new`]
let impl_24__new (#v_Idx: Type0) (start v_end: v_Idx) : t_RangeInclusive v_Idx =
  { f_start = start; f_end = v_end } <: t_RangeInclusive v_Idx

/// See [`std::ops::RangeInclusive::into_inner`]
let impl_24__into_inner (#v_Idx: Type0) (self: t_RangeInclusive v_Idx) : (v_Idx & v_Idx) =
  self.f_start, self.f_end <: (v_Idx & v_Idx)

/// See [`std::ops::RangeInclusive::start`]
let impl_25__start (#v_Idx: Type0) (self: t_RangeInclusive v_Idx) : v_Idx = self.f_start

/// See [`std::ops::RangeInclusive::end`]
let impl_25__end (#v_Idx: Type0) (self: t_RangeInclusive v_Idx) : v_Idx = self.f_end

/// See [`std::ops::FromResidual`]
class t_FromResidual (v_Self: Type0) (v_R: Type0) = {
  f_from_residual_pre:v_R -> Type0;
  f_from_residual_post:v_R -> v_Self -> Type0;
  f_from_residual:x0: v_R
    -> Prims.Pure v_Self (f_from_residual_pre x0) (fun result -> f_from_residual_post x0 result)
}

/// See [`std::ops::Yeet`]
type t_Yeet (v_T: Type0) = | Yeet : v_T -> t_Yeet v_T

/// See [`std::option::Option`]
type t_Option (v_T: Type0) =
  | Option_Some : v_T -> t_Option v_T
  | Option_None : t_Option v_T

/// See [`std::iter::Chain`]
type t_Chain (v_A: Type0) (v_B: Type0) = {
  f_a:t_Option v_A;
  f_b:v_B
}

/// See [`std::iter::FlatMap`]
type t_FlatMap (v_I: Type0) (v_U: Type0) (v_F: Type0) = {
  f_it:v_I;
  f_f:v_F;
  f_current:t_Option v_U
}

/// See [`std::primitive::u8::checked_add`] (and similar for other integer types)
let impl_6__checked_add (x y: u8) : t_Option u8 =
  let (result: u8), (overflowed: bool) = impl_6__overflowing_add x y in
  if overflowed then Option_None <: t_Option u8 else Option_Some result <: t_Option u8

/// See [`std::primitive::u8::checked_sub`] (and similar for other integer types)
let impl_6__checked_sub (x y: u8) : t_Option u8 =
  let (result: u8), (overflowed: bool) = impl_6__overflowing_sub x y in
  if overflowed then Option_None <: t_Option u8 else Option_Some result <: t_Option u8

/// See [`std::primitive::u8::checked_mul`] (and similar for other integer types)
let impl_6__checked_mul (x y: u8) : t_Option u8 =
  let (result: u8), (overflowed: bool) = impl_6__overflowing_mul x y in
  if overflowed then Option_None <: t_Option u8 else Option_Some result <: t_Option u8

/// See [`std::primitive::u8::checked_div`] (and similar for other integer types)
let impl_6__checked_div (x y: u8) : t_Option u8 =
  if y =. mk_u8 0 then Option_None <: t_Option u8 else Option_Some (x /! y) <: t_Option u8

/// See [`std::primitive::u8::checked_rem`] (and similar for other integer types)
let impl_6__checked_rem (x y: u8) : t_Option u8 =
  if y =. mk_u8 0 then Option_None <: t_Option u8 else Option_Some (x %! y) <: t_Option u8

/// See [`std::primitive::u8::checked_ilog2`] (and similar for other integer types)
let impl_6__checked_ilog2 (x: u8) : t_Option u32 =
  if x =. mk_u8 0
  then Option_None <: t_Option u32
  else Option_Some (impl_6__ilog2 x) <: t_Option u32

/// See [`std::primitive::u8::checked_neg`] (and similar for other integer types)
let impl_6__checked_neg (x: u8) : t_Option u8 =
  if x =. mk_u8 0 then Option_Some (mk_u8 0) <: t_Option u8 else Option_None <: t_Option u8

/// See [`std::primitive::u8::checked_div_euclid`] (and similar for other unsigned integer types)
let impl_6__checked_div_euclid (x y: u8) : t_Option u8 =
  if y =. mk_u8 0 then Option_None <: t_Option u8 else Option_Some (x /! y) <: t_Option u8

/// See [`std::primitive::u8::checked_rem_euclid`] (and similar for other unsigned integer types)
let impl_6__checked_rem_euclid (x y: u8) : t_Option u8 =
  if y =. mk_u8 0 then Option_None <: t_Option u8 else Option_Some (x %! y) <: t_Option u8

/// See [`std::primitive::u8::div_exact`] (and similar for other unsigned integer types)
let impl_6__div_exact (x y: u8)
    : Prims.Pure (t_Option u8) (requires y <>. mk_u8 0) (fun _ -> Prims.l_True) =
  if (x %! y <: u8) <>. mk_u8 0
  then Option_None <: t_Option u8
  else Option_Some (x /! y) <: t_Option u8

/// See [`std::primitive::u8::checked_div_exact`] (and similar for other unsigned integer types)
let impl_6__checked_div_exact (x y: u8) : t_Option u8 =
  if y =. mk_u8 0 || (x %! y <: u8) <>. mk_u8 0
  then Option_None <: t_Option u8
  else Option_Some (x /! y) <: t_Option u8

/// See [`std::primitive::u8::checked_next_multiple_of`] (and similar for other unsigned integer types)
let impl_6__checked_next_multiple_of (x y: u8) : t_Option u8 =
  if y =. mk_u8 0
  then Option_None <: t_Option u8
  else impl_6__checked_add x ((y -! (x %! y <: u8) <: u8) %! y <: u8)

/// See [`std::primitive::u8::checked_signed_diff`] (and similar for other unsigned integer types)
let impl_6__checked_signed_diff (x y: u8) : t_Option i8 =
  let result:i8 = cast (impl_6__wrapping_sub x y <: u8) <: i8 in
  if (x >=. y <: bool) =. (result <. mk_i8 0 <: bool)
  then Option_None <: t_Option i8
  else Option_Some result <: t_Option i8

/// See [`std::primitive::u8::checked_add_signed`] (and similar for other unsigned integer types)
let impl_6__checked_add_signed (x: u8) (y: i8) : t_Option u8 =
  let (result: u8), (overflowed: bool) = impl_6__overflowing_add_signed x y in
  if overflowed then Option_None <: t_Option u8 else Option_Some result <: t_Option u8

/// See [`std::primitive::u8::checked_sub_signed`] (and similar for other unsigned integer types)
let impl_6__checked_sub_signed (x: u8) (y: i8) : t_Option u8 =
  let (result: u8), (overflowed: bool) = impl_6__overflowing_sub_signed x y in
  if overflowed then Option_None <: t_Option u8 else Option_Some result <: t_Option u8

/// See [`std::primitive::u8::highest_one`] (and similar for other unsigned integer types)
let impl_6__highest_one (x: u8) : t_Option u32 = impl_6__checked_ilog2 x

/// See [`std::primitive::u8::lowest_one`] (and similar for other integer types)
let impl_6__lowest_one (x: u8) : t_Option u32 =
  if x =. mk_u8 0
  then Option_None <: t_Option u32
  else Option_Some (impl_6__trailing_zeros x) <: t_Option u32

/// See [`std::primitive::u8::checked_shl`] (and similar for other integer types)
let impl_6__checked_shl (x: u8) (n: u32) : t_Option u8 =
  if n <. impl_6__BITS then Option_Some (x <<! n) <: t_Option u8 else Option_None <: t_Option u8

/// See [`std::primitive::u8::checked_shr`] (and similar for other integer types)
let impl_6__checked_shr (x: u8) (n: u32) : t_Option u8 =
  if n <. impl_6__BITS then Option_Some (x >>! n) <: t_Option u8 else Option_None <: t_Option u8

/// See [`std::primitive::u8::shl_exact`] (and similar for other unsigned integer types)
let impl_6__shl_exact (x: u8) (n: u32) : t_Option u8 =
  if n <=. (impl_6__leading_zeros x <: u32) && n <. impl_6__BITS
  then Option_Some (x <<! n) <: t_Option u8
  else Option_None <: t_Option u8

/// See [`std::primitive::u8::shr_exact`] (and similar for other integer types)
let impl_6__shr_exact (x: u8) (n: u32) : t_Option u8 =
  if n <=. (impl_6__trailing_zeros x <: u32) && n <. impl_6__BITS
  then Option_Some (x >>! n) <: t_Option u8
  else Option_None <: t_Option u8

/// See [`std::primitive::u8::checked_next_power_of_two`] (and similar for other unsigned integer types)
let impl_6__checked_next_power_of_two (x: u8) : t_Option u8 =
  if x <=. mk_u8 1
  then Option_Some (mk_u8 1) <: t_Option u8
  else
    impl_6__checked_add (impl_6__MAX >>!
        ((impl_6__leading_zeros (x -! mk_u8 1 <: u8) <: u32) %! impl_6__BITS <: u32)
        <:
        u8)
      (mk_u8 1)

/// See [`std::primitive::u8::checked_add`] (and similar for other integer types)
let impl_7__checked_add (x y: u16) : t_Option u16 =
  let (result: u16), (overflowed: bool) = impl_7__overflowing_add x y in
  if overflowed then Option_None <: t_Option u16 else Option_Some result <: t_Option u16

/// See [`std::primitive::u8::checked_sub`] (and similar for other integer types)
let impl_7__checked_sub (x y: u16) : t_Option u16 =
  let (result: u16), (overflowed: bool) = impl_7__overflowing_sub x y in
  if overflowed then Option_None <: t_Option u16 else Option_Some result <: t_Option u16

/// See [`std::primitive::u8::checked_mul`] (and similar for other integer types)
let impl_7__checked_mul (x y: u16) : t_Option u16 =
  let (result: u16), (overflowed: bool) = impl_7__overflowing_mul x y in
  if overflowed then Option_None <: t_Option u16 else Option_Some result <: t_Option u16

/// See [`std::primitive::u8::checked_div`] (and similar for other integer types)
let impl_7__checked_div (x y: u16) : t_Option u16 =
  if y =. mk_u16 0 then Option_None <: t_Option u16 else Option_Some (x /! y) <: t_Option u16

/// See [`std::primitive::u8::checked_rem`] (and similar for other integer types)
let impl_7__checked_rem (x y: u16) : t_Option u16 =
  if y =. mk_u16 0 then Option_None <: t_Option u16 else Option_Some (x %! y) <: t_Option u16

/// See [`std::primitive::u8::checked_ilog2`] (and similar for other integer types)
let impl_7__checked_ilog2 (x: u16) : t_Option u32 =
  if x =. mk_u16 0
  then Option_None <: t_Option u32
  else Option_Some (impl_7__ilog2 x) <: t_Option u32

/// See [`std::primitive::u8::checked_neg`] (and similar for other integer types)
let impl_7__checked_neg (x: u16) : t_Option u16 =
  if x =. mk_u16 0 then Option_Some (mk_u16 0) <: t_Option u16 else Option_None <: t_Option u16

/// See [`std::primitive::u8::checked_div_euclid`] (and similar for other unsigned integer types)
let impl_7__checked_div_euclid (x y: u16) : t_Option u16 =
  if y =. mk_u16 0 then Option_None <: t_Option u16 else Option_Some (x /! y) <: t_Option u16

/// See [`std::primitive::u8::checked_rem_euclid`] (and similar for other unsigned integer types)
let impl_7__checked_rem_euclid (x y: u16) : t_Option u16 =
  if y =. mk_u16 0 then Option_None <: t_Option u16 else Option_Some (x %! y) <: t_Option u16

/// See [`std::primitive::u8::div_exact`] (and similar for other unsigned integer types)
let impl_7__div_exact (x y: u16)
    : Prims.Pure (t_Option u16) (requires y <>. mk_u16 0) (fun _ -> Prims.l_True) =
  if (x %! y <: u16) <>. mk_u16 0
  then Option_None <: t_Option u16
  else Option_Some (x /! y) <: t_Option u16

/// See [`std::primitive::u8::checked_div_exact`] (and similar for other unsigned integer types)
let impl_7__checked_div_exact (x y: u16) : t_Option u16 =
  if y =. mk_u16 0 || (x %! y <: u16) <>. mk_u16 0
  then Option_None <: t_Option u16
  else Option_Some (x /! y) <: t_Option u16

/// See [`std::primitive::u8::checked_next_multiple_of`] (and similar for other unsigned integer types)
let impl_7__checked_next_multiple_of (x y: u16) : t_Option u16 =
  if y =. mk_u16 0
  then Option_None <: t_Option u16
  else impl_7__checked_add x ((y -! (x %! y <: u16) <: u16) %! y <: u16)

/// See [`std::primitive::u8::checked_signed_diff`] (and similar for other unsigned integer types)
let impl_7__checked_signed_diff (x y: u16) : t_Option i16 =
  let result:i16 = cast (impl_7__wrapping_sub x y <: u16) <: i16 in
  if (x >=. y <: bool) =. (result <. mk_i16 0 <: bool)
  then Option_None <: t_Option i16
  else Option_Some result <: t_Option i16

/// See [`std::primitive::u8::checked_add_signed`] (and similar for other unsigned integer types)
let impl_7__checked_add_signed (x: u16) (y: i16) : t_Option u16 =
  let (result: u16), (overflowed: bool) = impl_7__overflowing_add_signed x y in
  if overflowed then Option_None <: t_Option u16 else Option_Some result <: t_Option u16

/// See [`std::primitive::u8::checked_sub_signed`] (and similar for other unsigned integer types)
let impl_7__checked_sub_signed (x: u16) (y: i16) : t_Option u16 =
  let (result: u16), (overflowed: bool) = impl_7__overflowing_sub_signed x y in
  if overflowed then Option_None <: t_Option u16 else Option_Some result <: t_Option u16

/// See [`std::primitive::u8::highest_one`] (and similar for other unsigned integer types)
let impl_7__highest_one (x: u16) : t_Option u32 = impl_7__checked_ilog2 x

/// See [`std::primitive::u8::lowest_one`] (and similar for other integer types)
let impl_7__lowest_one (x: u16) : t_Option u32 =
  if x =. mk_u16 0
  then Option_None <: t_Option u32
  else Option_Some (impl_7__trailing_zeros x) <: t_Option u32

/// See [`std::primitive::u8::checked_shl`] (and similar for other integer types)
let impl_7__checked_shl (x: u16) (n: u32) : t_Option u16 =
  if n <. impl_7__BITS then Option_Some (x <<! n) <: t_Option u16 else Option_None <: t_Option u16

/// See [`std::primitive::u8::checked_shr`] (and similar for other integer types)
let impl_7__checked_shr (x: u16) (n: u32) : t_Option u16 =
  if n <. impl_7__BITS then Option_Some (x >>! n) <: t_Option u16 else Option_None <: t_Option u16

/// See [`std::primitive::u8::shl_exact`] (and similar for other unsigned integer types)
let impl_7__shl_exact (x: u16) (n: u32) : t_Option u16 =
  if n <=. (impl_7__leading_zeros x <: u32) && n <. impl_7__BITS
  then Option_Some (x <<! n) <: t_Option u16
  else Option_None <: t_Option u16

/// See [`std::primitive::u8::shr_exact`] (and similar for other integer types)
let impl_7__shr_exact (x: u16) (n: u32) : t_Option u16 =
  if n <=. (impl_7__trailing_zeros x <: u32) && n <. impl_7__BITS
  then Option_Some (x >>! n) <: t_Option u16
  else Option_None <: t_Option u16

/// See [`std::primitive::u8::checked_next_power_of_two`] (and similar for other unsigned integer types)
let impl_7__checked_next_power_of_two (x: u16) : t_Option u16 =
  if x <=. mk_u16 1
  then Option_Some (mk_u16 1) <: t_Option u16
  else
    impl_7__checked_add (impl_7__MAX >>!
        ((impl_7__leading_zeros (x -! mk_u16 1 <: u16) <: u32) %! impl_7__BITS <: u32)
        <:
        u16)
      (mk_u16 1)

/// See [`std::primitive::u8::checked_add`] (and similar for other integer types)
let impl_8__checked_add (x y: u32) : t_Option u32 =
  let (result: u32), (overflowed: bool) = impl_8__overflowing_add x y in
  if overflowed then Option_None <: t_Option u32 else Option_Some result <: t_Option u32

/// See [`std::primitive::u8::checked_sub`] (and similar for other integer types)
let impl_8__checked_sub (x y: u32) : t_Option u32 =
  let (result: u32), (overflowed: bool) = impl_8__overflowing_sub x y in
  if overflowed then Option_None <: t_Option u32 else Option_Some result <: t_Option u32

/// See [`std::primitive::u8::checked_mul`] (and similar for other integer types)
let impl_8__checked_mul (x y: u32) : t_Option u32 =
  let (result: u32), (overflowed: bool) = impl_8__overflowing_mul x y in
  if overflowed then Option_None <: t_Option u32 else Option_Some result <: t_Option u32

/// See [`std::primitive::u8::checked_div`] (and similar for other integer types)
let impl_8__checked_div (x y: u32) : t_Option u32 =
  if y =. mk_u32 0 then Option_None <: t_Option u32 else Option_Some (x /! y) <: t_Option u32

/// See [`std::primitive::u8::checked_rem`] (and similar for other integer types)
let impl_8__checked_rem (x y: u32) : t_Option u32 =
  if y =. mk_u32 0 then Option_None <: t_Option u32 else Option_Some (x %! y) <: t_Option u32

/// See [`std::primitive::u8::checked_ilog2`] (and similar for other integer types)
let impl_8__checked_ilog2 (x: u32) : t_Option u32 =
  if x =. mk_u32 0
  then Option_None <: t_Option u32
  else Option_Some (impl_8__ilog2 x) <: t_Option u32

/// See [`std::primitive::u8::checked_neg`] (and similar for other integer types)
let impl_8__checked_neg (x: u32) : t_Option u32 =
  if x =. mk_u32 0 then Option_Some (mk_u32 0) <: t_Option u32 else Option_None <: t_Option u32

/// See [`std::primitive::u8::checked_div_euclid`] (and similar for other unsigned integer types)
let impl_8__checked_div_euclid (x y: u32) : t_Option u32 =
  if y =. mk_u32 0 then Option_None <: t_Option u32 else Option_Some (x /! y) <: t_Option u32

/// See [`std::primitive::u8::checked_rem_euclid`] (and similar for other unsigned integer types)
let impl_8__checked_rem_euclid (x y: u32) : t_Option u32 =
  if y =. mk_u32 0 then Option_None <: t_Option u32 else Option_Some (x %! y) <: t_Option u32

/// See [`std::primitive::u8::div_exact`] (and similar for other unsigned integer types)
let impl_8__div_exact (x y: u32)
    : Prims.Pure (t_Option u32) (requires y <>. mk_u32 0) (fun _ -> Prims.l_True) =
  if (x %! y <: u32) <>. mk_u32 0
  then Option_None <: t_Option u32
  else Option_Some (x /! y) <: t_Option u32

/// See [`std::primitive::u8::checked_div_exact`] (and similar for other unsigned integer types)
let impl_8__checked_div_exact (x y: u32) : t_Option u32 =
  if y =. mk_u32 0 || (x %! y <: u32) <>. mk_u32 0
  then Option_None <: t_Option u32
  else Option_Some (x /! y) <: t_Option u32

/// See [`std::primitive::u8::checked_next_multiple_of`] (and similar for other unsigned integer types)
let impl_8__checked_next_multiple_of (x y: u32) : t_Option u32 =
  if y =. mk_u32 0
  then Option_None <: t_Option u32
  else impl_8__checked_add x ((y -! (x %! y <: u32) <: u32) %! y <: u32)

/// See [`std::primitive::u8::checked_signed_diff`] (and similar for other unsigned integer types)
let impl_8__checked_signed_diff (x y: u32) : t_Option i32 =
  let result:i32 = cast (impl_8__wrapping_sub x y <: u32) <: i32 in
  if (x >=. y <: bool) =. (result <. mk_i32 0 <: bool)
  then Option_None <: t_Option i32
  else Option_Some result <: t_Option i32

/// See [`std::primitive::u8::checked_add_signed`] (and similar for other unsigned integer types)
let impl_8__checked_add_signed (x: u32) (y: i32) : t_Option u32 =
  let (result: u32), (overflowed: bool) = impl_8__overflowing_add_signed x y in
  if overflowed then Option_None <: t_Option u32 else Option_Some result <: t_Option u32

/// See [`std::primitive::u8::checked_sub_signed`] (and similar for other unsigned integer types)
let impl_8__checked_sub_signed (x: u32) (y: i32) : t_Option u32 =
  let (result: u32), (overflowed: bool) = impl_8__overflowing_sub_signed x y in
  if overflowed then Option_None <: t_Option u32 else Option_Some result <: t_Option u32

/// See [`std::primitive::u8::highest_one`] (and similar for other unsigned integer types)
let impl_8__highest_one (x: u32) : t_Option u32 = impl_8__checked_ilog2 x

/// See [`std::primitive::u8::lowest_one`] (and similar for other integer types)
let impl_8__lowest_one (x: u32) : t_Option u32 =
  if x =. mk_u32 0
  then Option_None <: t_Option u32
  else Option_Some (impl_8__trailing_zeros x) <: t_Option u32

/// See [`std::primitive::u8::checked_shl`] (and similar for other integer types)
let impl_8__checked_shl (x n: u32) : t_Option u32 =
  if n <. impl_8__BITS then Option_Some (x <<! n) <: t_Option u32 else Option_None <: t_Option u32

/// See [`std::primitive::u8::checked_shr`] (and similar for other integer types)
let impl_8__checked_shr (x n: u32) : t_Option u32 =
  if n <. impl_8__BITS then Option_Some (x >>! n) <: t_Option u32 else Option_None <: t_Option u32

/// See [`std::primitive::u8::shl_exact`] (and similar for other unsigned integer types)
let impl_8__shl_exact (x n: u32) : t_Option u32 =
  if n <=. (impl_8__leading_zeros x <: u32) && n <. impl_8__BITS
  then Option_Some (x <<! n) <: t_Option u32
  else Option_None <: t_Option u32

/// See [`std::primitive::u8::shr_exact`] (and similar for other integer types)
let impl_8__shr_exact (x n: u32) : t_Option u32 =
  if n <=. (impl_8__trailing_zeros x <: u32) && n <. impl_8__BITS
  then Option_Some (x >>! n) <: t_Option u32
  else Option_None <: t_Option u32

/// See [`std::primitive::u8::checked_next_power_of_two`] (and similar for other unsigned integer types)
let impl_8__checked_next_power_of_two (x: u32) : t_Option u32 =
  if x <=. mk_u32 1
  then Option_Some (mk_u32 1) <: t_Option u32
  else
    impl_8__checked_add (impl_8__MAX >>!
        ((impl_8__leading_zeros (x -! mk_u32 1 <: u32) <: u32) %! impl_8__BITS <: u32)
        <:
        u32)
      (mk_u32 1)

/// See [`std::primitive::u8::checked_add`] (and similar for other integer types)
let impl_9__checked_add (x y: u64) : t_Option u64 =
  let (result: u64), (overflowed: bool) = impl_9__overflowing_add x y in
  if overflowed then Option_None <: t_Option u64 else Option_Some result <: t_Option u64

/// See [`std::primitive::u8::checked_sub`] (and similar for other integer types)
let impl_9__checked_sub (x y: u64) : t_Option u64 =
  let (result: u64), (overflowed: bool) = impl_9__overflowing_sub x y in
  if overflowed then Option_None <: t_Option u64 else Option_Some result <: t_Option u64

/// See [`std::primitive::u8::checked_mul`] (and similar for other integer types)
let impl_9__checked_mul (x y: u64) : t_Option u64 =
  let (result: u64), (overflowed: bool) = impl_9__overflowing_mul x y in
  if overflowed then Option_None <: t_Option u64 else Option_Some result <: t_Option u64

/// See [`std::primitive::u8::checked_div`] (and similar for other integer types)
let impl_9__checked_div (x y: u64) : t_Option u64 =
  if y =. mk_u64 0 then Option_None <: t_Option u64 else Option_Some (x /! y) <: t_Option u64

/// See [`std::primitive::u8::checked_rem`] (and similar for other integer types)
let impl_9__checked_rem (x y: u64) : t_Option u64 =
  if y =. mk_u64 0 then Option_None <: t_Option u64 else Option_Some (x %! y) <: t_Option u64

/// See [`std::primitive::u8::checked_ilog2`] (and similar for other integer types)
let impl_9__checked_ilog2 (x: u64) : t_Option u32 =
  if x =. mk_u64 0
  then Option_None <: t_Option u32
  else Option_Some (impl_9__ilog2 x) <: t_Option u32

/// See [`std::primitive::u8::checked_neg`] (and similar for other integer types)
let impl_9__checked_neg (x: u64) : t_Option u64 =
  if x =. mk_u64 0 then Option_Some (mk_u64 0) <: t_Option u64 else Option_None <: t_Option u64

/// See [`std::primitive::u8::checked_div_euclid`] (and similar for other unsigned integer types)
let impl_9__checked_div_euclid (x y: u64) : t_Option u64 =
  if y =. mk_u64 0 then Option_None <: t_Option u64 else Option_Some (x /! y) <: t_Option u64

/// See [`std::primitive::u8::checked_rem_euclid`] (and similar for other unsigned integer types)
let impl_9__checked_rem_euclid (x y: u64) : t_Option u64 =
  if y =. mk_u64 0 then Option_None <: t_Option u64 else Option_Some (x %! y) <: t_Option u64

/// See [`std::primitive::u8::div_exact`] (and similar for other unsigned integer types)
let impl_9__div_exact (x y: u64)
    : Prims.Pure (t_Option u64) (requires y <>. mk_u64 0) (fun _ -> Prims.l_True) =
  if (x %! y <: u64) <>. mk_u64 0
  then Option_None <: t_Option u64
  else Option_Some (x /! y) <: t_Option u64

/// See [`std::primitive::u8::checked_div_exact`] (and similar for other unsigned integer types)
let impl_9__checked_div_exact (x y: u64) : t_Option u64 =
  if y =. mk_u64 0 || (x %! y <: u64) <>. mk_u64 0
  then Option_None <: t_Option u64
  else Option_Some (x /! y) <: t_Option u64

/// See [`std::primitive::u8::checked_next_multiple_of`] (and similar for other unsigned integer types)
let impl_9__checked_next_multiple_of (x y: u64) : t_Option u64 =
  if y =. mk_u64 0
  then Option_None <: t_Option u64
  else impl_9__checked_add x ((y -! (x %! y <: u64) <: u64) %! y <: u64)

/// See [`std::primitive::u8::checked_signed_diff`] (and similar for other unsigned integer types)
let impl_9__checked_signed_diff (x y: u64) : t_Option i64 =
  let result:i64 = cast (impl_9__wrapping_sub x y <: u64) <: i64 in
  if (x >=. y <: bool) =. (result <. mk_i64 0 <: bool)
  then Option_None <: t_Option i64
  else Option_Some result <: t_Option i64

/// See [`std::primitive::u8::checked_add_signed`] (and similar for other unsigned integer types)
let impl_9__checked_add_signed (x: u64) (y: i64) : t_Option u64 =
  let (result: u64), (overflowed: bool) = impl_9__overflowing_add_signed x y in
  if overflowed then Option_None <: t_Option u64 else Option_Some result <: t_Option u64

/// See [`std::primitive::u8::checked_sub_signed`] (and similar for other unsigned integer types)
let impl_9__checked_sub_signed (x: u64) (y: i64) : t_Option u64 =
  let (result: u64), (overflowed: bool) = impl_9__overflowing_sub_signed x y in
  if overflowed then Option_None <: t_Option u64 else Option_Some result <: t_Option u64

/// See [`std::primitive::u8::highest_one`] (and similar for other unsigned integer types)
let impl_9__highest_one (x: u64) : t_Option u32 = impl_9__checked_ilog2 x

/// See [`std::primitive::u8::lowest_one`] (and similar for other integer types)
let impl_9__lowest_one (x: u64) : t_Option u32 =
  if x =. mk_u64 0
  then Option_None <: t_Option u32
  else Option_Some (impl_9__trailing_zeros x) <: t_Option u32

/// See [`std::primitive::u8::checked_shl`] (and similar for other integer types)
let impl_9__checked_shl (x: u64) (n: u32) : t_Option u64 =
  if n <. impl_9__BITS then Option_Some (x <<! n) <: t_Option u64 else Option_None <: t_Option u64

/// See [`std::primitive::u8::checked_shr`] (and similar for other integer types)
let impl_9__checked_shr (x: u64) (n: u32) : t_Option u64 =
  if n <. impl_9__BITS then Option_Some (x >>! n) <: t_Option u64 else Option_None <: t_Option u64

/// See [`std::primitive::u8::shl_exact`] (and similar for other unsigned integer types)
let impl_9__shl_exact (x: u64) (n: u32) : t_Option u64 =
  if n <=. (impl_9__leading_zeros x <: u32) && n <. impl_9__BITS
  then Option_Some (x <<! n) <: t_Option u64
  else Option_None <: t_Option u64

/// See [`std::primitive::u8::shr_exact`] (and similar for other integer types)
let impl_9__shr_exact (x: u64) (n: u32) : t_Option u64 =
  if n <=. (impl_9__trailing_zeros x <: u32) && n <. impl_9__BITS
  then Option_Some (x >>! n) <: t_Option u64
  else Option_None <: t_Option u64

/// See [`std::primitive::u8::checked_next_power_of_two`] (and similar for other unsigned integer types)
let impl_9__checked_next_power_of_two (x: u64) : t_Option u64 =
  if x <=. mk_u64 1
  then Option_Some (mk_u64 1) <: t_Option u64
  else
    impl_9__checked_add (impl_9__MAX >>!
        ((impl_9__leading_zeros (x -! mk_u64 1 <: u64) <: u32) %! impl_9__BITS <: u32)
        <:
        u64)
      (mk_u64 1)

/// See [`std::primitive::u8::checked_add`] (and similar for other integer types)
let impl_10__checked_add (x y: u128) : t_Option u128 =
  let (result: u128), (overflowed: bool) = impl_10__overflowing_add x y in
  if overflowed then Option_None <: t_Option u128 else Option_Some result <: t_Option u128

/// See [`std::primitive::u8::checked_sub`] (and similar for other integer types)
let impl_10__checked_sub (x y: u128) : t_Option u128 =
  let (result: u128), (overflowed: bool) = impl_10__overflowing_sub x y in
  if overflowed then Option_None <: t_Option u128 else Option_Some result <: t_Option u128

/// See [`std::primitive::u8::checked_mul`] (and similar for other integer types)
let impl_10__checked_mul (x y: u128) : t_Option u128 =
  let (result: u128), (overflowed: bool) = impl_10__overflowing_mul x y in
  if overflowed then Option_None <: t_Option u128 else Option_Some result <: t_Option u128

/// See [`std::primitive::u8::checked_div`] (and similar for other integer types)
let impl_10__checked_div (x y: u128) : t_Option u128 =
  if y =. mk_u128 0 then Option_None <: t_Option u128 else Option_Some (x /! y) <: t_Option u128

/// See [`std::primitive::u8::checked_rem`] (and similar for other integer types)
let impl_10__checked_rem (x y: u128) : t_Option u128 =
  if y =. mk_u128 0 then Option_None <: t_Option u128 else Option_Some (x %! y) <: t_Option u128

/// See [`std::primitive::u8::checked_ilog2`] (and similar for other integer types)
let impl_10__checked_ilog2 (x: u128) : t_Option u32 =
  if x =. mk_u128 0
  then Option_None <: t_Option u32
  else Option_Some (impl_10__ilog2 x) <: t_Option u32

/// See [`std::primitive::u8::checked_neg`] (and similar for other integer types)
let impl_10__checked_neg (x: u128) : t_Option u128 =
  if x =. mk_u128 0 then Option_Some (mk_u128 0) <: t_Option u128 else Option_None <: t_Option u128

/// See [`std::primitive::u8::checked_div_euclid`] (and similar for other unsigned integer types)
let impl_10__checked_div_euclid (x y: u128) : t_Option u128 =
  if y =. mk_u128 0 then Option_None <: t_Option u128 else Option_Some (x /! y) <: t_Option u128

/// See [`std::primitive::u8::checked_rem_euclid`] (and similar for other unsigned integer types)
let impl_10__checked_rem_euclid (x y: u128) : t_Option u128 =
  if y =. mk_u128 0 then Option_None <: t_Option u128 else Option_Some (x %! y) <: t_Option u128

/// See [`std::primitive::u8::div_exact`] (and similar for other unsigned integer types)
let impl_10__div_exact (x y: u128)
    : Prims.Pure (t_Option u128) (requires y <>. mk_u128 0) (fun _ -> Prims.l_True) =
  if (x %! y <: u128) <>. mk_u128 0
  then Option_None <: t_Option u128
  else Option_Some (x /! y) <: t_Option u128

/// See [`std::primitive::u8::checked_div_exact`] (and similar for other unsigned integer types)
let impl_10__checked_div_exact (x y: u128) : t_Option u128 =
  if y =. mk_u128 0 || (x %! y <: u128) <>. mk_u128 0
  then Option_None <: t_Option u128
  else Option_Some (x /! y) <: t_Option u128

/// See [`std::primitive::u8::checked_next_multiple_of`] (and similar for other unsigned integer types)
let impl_10__checked_next_multiple_of (x y: u128) : t_Option u128 =
  if y =. mk_u128 0
  then Option_None <: t_Option u128
  else impl_10__checked_add x ((y -! (x %! y <: u128) <: u128) %! y <: u128)

/// See [`std::primitive::u8::checked_signed_diff`] (and similar for other unsigned integer types)
let impl_10__checked_signed_diff (x y: u128) : t_Option i128 =
  let result:i128 = cast (impl_10__wrapping_sub x y <: u128) <: i128 in
  if (x >=. y <: bool) =. (result <. mk_i128 0 <: bool)
  then Option_None <: t_Option i128
  else Option_Some result <: t_Option i128

/// See [`std::primitive::u8::checked_add_signed`] (and similar for other unsigned integer types)
let impl_10__checked_add_signed (x: u128) (y: i128) : t_Option u128 =
  let (result: u128), (overflowed: bool) = impl_10__overflowing_add_signed x y in
  if overflowed then Option_None <: t_Option u128 else Option_Some result <: t_Option u128

/// See [`std::primitive::u8::checked_sub_signed`] (and similar for other unsigned integer types)
let impl_10__checked_sub_signed (x: u128) (y: i128) : t_Option u128 =
  let (result: u128), (overflowed: bool) = impl_10__overflowing_sub_signed x y in
  if overflowed then Option_None <: t_Option u128 else Option_Some result <: t_Option u128

/// See [`std::primitive::u8::highest_one`] (and similar for other unsigned integer types)
let impl_10__highest_one (x: u128) : t_Option u32 = impl_10__checked_ilog2 x

/// See [`std::primitive::u8::lowest_one`] (and similar for other integer types)
let impl_10__lowest_one (x: u128) : t_Option u32 =
  if x =. mk_u128 0
  then Option_None <: t_Option u32
  else Option_Some (impl_10__trailing_zeros x) <: t_Option u32

/// See [`std::primitive::u8::checked_shl`] (and similar for other integer types)
let impl_10__checked_shl (x: u128) (n: u32) : t_Option u128 =
  if n <. impl_10__BITS
  then Option_Some (x <<! n) <: t_Option u128
  else Option_None <: t_Option u128

/// See [`std::primitive::u8::checked_shr`] (and similar for other integer types)
let impl_10__checked_shr (x: u128) (n: u32) : t_Option u128 =
  if n <. impl_10__BITS
  then Option_Some (x >>! n) <: t_Option u128
  else Option_None <: t_Option u128

/// See [`std::primitive::u8::shl_exact`] (and similar for other unsigned integer types)
let impl_10__shl_exact (x: u128) (n: u32) : t_Option u128 =
  if n <=. (impl_10__leading_zeros x <: u32) && n <. impl_10__BITS
  then Option_Some (x <<! n) <: t_Option u128
  else Option_None <: t_Option u128

/// See [`std::primitive::u8::shr_exact`] (and similar for other integer types)
let impl_10__shr_exact (x: u128) (n: u32) : t_Option u128 =
  if n <=. (impl_10__trailing_zeros x <: u32) && n <. impl_10__BITS
  then Option_Some (x >>! n) <: t_Option u128
  else Option_None <: t_Option u128

/// See [`std::primitive::u8::checked_next_power_of_two`] (and similar for other unsigned integer types)
let impl_10__checked_next_power_of_two (x: u128) : t_Option u128 =
  if x <=. mk_u128 1
  then Option_Some (mk_u128 1) <: t_Option u128
  else
    impl_10__checked_add (impl_10__MAX >>!
        ((impl_10__leading_zeros (x -! mk_u128 1 <: u128) <: u32) %! impl_10__BITS <: u32)
        <:
        u128)
      (mk_u128 1)

/// See [`std::primitive::u8::checked_add`] (and similar for other integer types)
let impl_11__checked_add (x y: usize) : t_Option usize =
  let (result: usize), (overflowed: bool) = impl_11__overflowing_add x y in
  if overflowed then Option_None <: t_Option usize else Option_Some result <: t_Option usize

/// See [`std::primitive::u8::checked_sub`] (and similar for other integer types)
let impl_11__checked_sub (x y: usize) : t_Option usize =
  let (result: usize), (overflowed: bool) = impl_11__overflowing_sub x y in
  if overflowed then Option_None <: t_Option usize else Option_Some result <: t_Option usize

/// See [`std::primitive::u8::checked_mul`] (and similar for other integer types)
let impl_11__checked_mul (x y: usize) : t_Option usize =
  let (result: usize), (overflowed: bool) = impl_11__overflowing_mul x y in
  if overflowed then Option_None <: t_Option usize else Option_Some result <: t_Option usize

/// See [`std::primitive::u8::checked_div`] (and similar for other integer types)
let impl_11__checked_div (x y: usize) : t_Option usize =
  if y =. mk_usize 0 then Option_None <: t_Option usize else Option_Some (x /! y) <: t_Option usize

/// See [`std::primitive::u8::checked_rem`] (and similar for other integer types)
let impl_11__checked_rem (x y: usize) : t_Option usize =
  if y =. mk_usize 0 then Option_None <: t_Option usize else Option_Some (x %! y) <: t_Option usize

/// See [`std::primitive::u8::checked_ilog2`] (and similar for other integer types)
let impl_11__checked_ilog2 (x: usize) : t_Option u32 =
  if x =. mk_usize 0
  then Option_None <: t_Option u32
  else Option_Some (impl_11__ilog2 x) <: t_Option u32

/// See [`std::primitive::u8::checked_neg`] (and similar for other integer types)
let impl_11__checked_neg (x: usize) : t_Option usize =
  if x =. mk_usize 0
  then Option_Some (mk_usize 0) <: t_Option usize
  else Option_None <: t_Option usize

/// See [`std::primitive::u8::checked_div_euclid`] (and similar for other unsigned integer types)
let impl_11__checked_div_euclid (x y: usize) : t_Option usize =
  if y =. mk_usize 0 then Option_None <: t_Option usize else Option_Some (x /! y) <: t_Option usize

/// See [`std::primitive::u8::checked_rem_euclid`] (and similar for other unsigned integer types)
let impl_11__checked_rem_euclid (x y: usize) : t_Option usize =
  if y =. mk_usize 0 then Option_None <: t_Option usize else Option_Some (x %! y) <: t_Option usize

/// See [`std::primitive::u8::div_exact`] (and similar for other unsigned integer types)
let impl_11__div_exact (x y: usize)
    : Prims.Pure (t_Option usize) (requires y <>. mk_usize 0) (fun _ -> Prims.l_True) =
  if (x %! y <: usize) <>. mk_usize 0
  then Option_None <: t_Option usize
  else Option_Some (x /! y) <: t_Option usize

/// See [`std::primitive::u8::checked_div_exact`] (and similar for other unsigned integer types)
let impl_11__checked_div_exact (x y: usize) : t_Option usize =
  if y =. mk_usize 0 || (x %! y <: usize) <>. mk_usize 0
  then Option_None <: t_Option usize
  else Option_Some (x /! y) <: t_Option usize

/// See [`std::primitive::u8::checked_next_multiple_of`] (and similar for other unsigned integer types)
let impl_11__checked_next_multiple_of (x y: usize) : t_Option usize =
  if y =. mk_usize 0
  then Option_None <: t_Option usize
  else impl_11__checked_add x ((y -! (x %! y <: usize) <: usize) %! y <: usize)

/// See [`std::primitive::u8::checked_signed_diff`] (and similar for other unsigned integer types)
let impl_11__checked_signed_diff (x y: usize) : t_Option isize =
  let result:isize = cast (impl_11__wrapping_sub x y <: usize) <: isize in
  if (x >=. y <: bool) =. (result <. mk_isize 0 <: bool)
  then Option_None <: t_Option isize
  else Option_Some result <: t_Option isize

/// See [`std::primitive::u8::checked_add_signed`] (and similar for other unsigned integer types)
let impl_11__checked_add_signed (x: usize) (y: isize) : t_Option usize =
  let (result: usize), (overflowed: bool) = impl_11__overflowing_add_signed x y in
  if overflowed then Option_None <: t_Option usize else Option_Some result <: t_Option usize

/// See [`std::primitive::u8::checked_sub_signed`] (and similar for other unsigned integer types)
let impl_11__checked_sub_signed (x: usize) (y: isize) : t_Option usize =
  let (result: usize), (overflowed: bool) = impl_11__overflowing_sub_signed x y in
  if overflowed then Option_None <: t_Option usize else Option_Some result <: t_Option usize

/// See [`std::primitive::u8::highest_one`] (and similar for other unsigned integer types)
let impl_11__highest_one (x: usize) : t_Option u32 = impl_11__checked_ilog2 x

/// See [`std::primitive::u8::lowest_one`] (and similar for other integer types)
let impl_11__lowest_one (x: usize) : t_Option u32 =
  if x =. mk_usize 0
  then Option_None <: t_Option u32
  else Option_Some (impl_11__trailing_zeros x) <: t_Option u32

/// See [`std::primitive::u8::checked_shl`] (and similar for other integer types)
let impl_11__checked_shl (x: usize) (n: u32) : t_Option usize =
  if n <. impl_11__BITS
  then Option_Some (x <<! n) <: t_Option usize
  else Option_None <: t_Option usize

/// See [`std::primitive::u8::checked_shr`] (and similar for other integer types)
let impl_11__checked_shr (x: usize) (n: u32) : t_Option usize =
  if n <. impl_11__BITS
  then Option_Some (x >>! n) <: t_Option usize
  else Option_None <: t_Option usize

/// See [`std::primitive::u8::shl_exact`] (and similar for other unsigned integer types)
let impl_11__shl_exact (x: usize) (n: u32) : t_Option usize =
  if n <=. (impl_11__leading_zeros x <: u32) && n <. impl_11__BITS
  then Option_Some (x <<! n) <: t_Option usize
  else Option_None <: t_Option usize

/// See [`std::primitive::u8::shr_exact`] (and similar for other integer types)
let impl_11__shr_exact (x: usize) (n: u32) : t_Option usize =
  if n <=. (impl_11__trailing_zeros x <: u32) && n <. impl_11__BITS
  then Option_Some (x >>! n) <: t_Option usize
  else Option_None <: t_Option usize

/// See [`std::primitive::u8::checked_next_power_of_two`] (and similar for other unsigned integer types)
let impl_11__checked_next_power_of_two (x: usize) : t_Option usize =
  if x <=. mk_usize 1
  then Option_Some (mk_usize 1) <: t_Option usize
  else
    impl_11__checked_add (impl_11__MAX >>!
        ((impl_11__leading_zeros (x -! mk_usize 1 <: usize) <: u32) %! impl_11__BITS <: u32)
        <:
        usize)
      (mk_usize 1)

/// See [`std::primitive::u8::checked_add`] (and similar for other integer types)
let impl_12__checked_add (x y: i8) : t_Option i8 =
  let (result: i8), (overflowed: bool) = impl_12__overflowing_add x y in
  if overflowed then Option_None <: t_Option i8 else Option_Some result <: t_Option i8

/// See [`std::primitive::u8::checked_sub`] (and similar for other integer types)
let impl_12__checked_sub (x y: i8) : t_Option i8 =
  let (result: i8), (overflowed: bool) = impl_12__overflowing_sub x y in
  if overflowed then Option_None <: t_Option i8 else Option_Some result <: t_Option i8

/// See [`std::primitive::i8::checked_add_unsigned`] (and similar for other signed integer types)
let impl_12__checked_add_unsigned (x: i8) (y: u8) : t_Option i8 =
  let (result: i8), (overflowed: bool) = impl_12__overflowing_add x (cast (y <: u8) <: i8) in
  if overflowed =. (y >. (cast (impl_12__MAX <: i8) <: u8) <: bool)
  then Option_Some result <: t_Option i8
  else Option_None <: t_Option i8

/// See [`std::primitive::i8::checked_sub_unsigned`] (and similar for other signed integer types)
let impl_12__checked_sub_unsigned (x: i8) (y: u8) : t_Option i8 =
  let (result: i8), (overflowed: bool) = impl_12__overflowing_sub x (cast (y <: u8) <: i8) in
  if overflowed =. (y >. (cast (impl_12__MAX <: i8) <: u8) <: bool)
  then Option_Some result <: t_Option i8
  else Option_None <: t_Option i8

/// See [`std::primitive::u8::checked_mul`] (and similar for other integer types)
let impl_12__checked_mul (x y: i8) : t_Option i8 =
  let (result: i8), (overflowed: bool) = impl_12__overflowing_mul x y in
  if overflowed then Option_None <: t_Option i8 else Option_Some result <: t_Option i8

/// See [`std::primitive::i8::checked_div`] (and similar for other signed integer types)
let impl_12__checked_div (x y: i8) : t_Option i8 =
  if y =. mk_i8 0 || x =. impl_12__MIN && y =. mk_i8 (-1)
  then Option_None <: t_Option i8
  else Option_Some (x /! y) <: t_Option i8

/// See [`std::primitive::i8::checked_rem`] (and similar for other signed integer types)
let impl_12__checked_rem (x y: i8) : t_Option i8 =
  if y =. mk_i8 0 || x =. impl_12__MIN && y =. mk_i8 (-1)
  then Option_None <: t_Option i8
  else Option_Some (x %! y) <: t_Option i8

/// See [`std::primitive::i8::checked_ilog2`] (and similar for other integer types)
let impl_12__checked_ilog2 (x: i8) : t_Option u32 =
  if x <=. mk_i8 0
  then Option_None <: t_Option u32
  else Option_Some (impl_12__ilog2 x) <: t_Option u32

/// See [`std::primitive::i8::checked_neg`] (and similar for other integer types)
let impl_12__checked_neg (x: i8) : t_Option i8 =
  if x =. impl_12__MIN
  then Option_None <: t_Option i8
  else Option_Some (impl_12__wrapping_neg x) <: t_Option i8

/// See [`std::primitive::i8::checked_abs`] (and similar for other signed integer types)
let impl_12__checked_abs (x: i8) : t_Option i8 =
  if x <. mk_i8 0 then impl_12__checked_neg x else Option_Some x <: t_Option i8

/// See [`std::primitive::i8::checked_div_euclid`] (and similar for other signed integer types)
let impl_12__checked_div_euclid (x y: i8) : t_Option i8 =
  if y =. mk_i8 0 || x =. impl_12__MIN && y =. mk_i8 (-1)
  then Option_None <: t_Option i8
  else Option_Some (impl_12__div_euclid x y) <: t_Option i8

/// See [`std::primitive::i8::checked_rem_euclid`] (and similar for other signed integer types)
let impl_12__checked_rem_euclid (x y: i8) : t_Option i8 =
  if y =. mk_i8 0 || x =. impl_12__MIN && y =. mk_i8 (-1)
  then Option_None <: t_Option i8
  else Option_Some (impl_12__rem_euclid x y) <: t_Option i8

/// See [`std::primitive::i8::div_exact`] (and similar for other signed integer types)
let impl_12__div_exact (x y: i8)
    : Prims.Pure (t_Option i8)
      (requires y <>. mk_i8 0 && ~.((x =. impl_12__MIN <: bool) && (y =. mk_i8 (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  if (x %! y <: i8) <>. mk_i8 0
  then Option_None <: t_Option i8
  else Option_Some (x /! y) <: t_Option i8

/// See [`std::primitive::i8::checked_div_exact`] (and similar for other signed integer types)
let impl_12__checked_div_exact (x y: i8) : t_Option i8 =
  if y =. mk_i8 0 || x =. impl_12__MIN && y =. mk_i8 (-1) || (x %! y <: i8) <>. mk_i8 0
  then Option_None <: t_Option i8
  else Option_Some (x /! y) <: t_Option i8

/// See [`std::primitive::i8::checked_next_multiple_of`] (and similar for other signed integer types)
let impl_12__checked_next_multiple_of (x y: i8) : t_Option i8 =
  if y =. mk_i8 (-1)
  then Option_Some x <: t_Option i8
  else
    if y =. mk_i8 0
    then Option_None <: t_Option i8
    else
      let r:i8 = x %! y in
      let m:i8 =
        if r >. mk_i8 0 && y <. mk_i8 0 || r <. mk_i8 0 && y >. mk_i8 0
        then impl_12__wrapping_add r y
        else r
      in
      if m =. mk_i8 0
      then Option_Some x <: t_Option i8
      else impl_12__checked_add x (impl_12__wrapping_sub y m <: i8)

/// See [`std::primitive::i8::highest_one`] (and similar for other signed integer types)
assume
val impl_12__highest_one': x: i8 -> t_Option u32

unfold
let impl_12__highest_one = impl_12__highest_one'

/// See [`std::primitive::i8::lowest_one`] (and similar for other integer types)
let impl_12__lowest_one (x: i8) : t_Option u32 =
  if x =. mk_i8 0
  then Option_None <: t_Option u32
  else Option_Some (impl_12__trailing_zeros x) <: t_Option u32

/// See [`std::primitive::i8::checked_shl`] (and similar for other integer types)
let impl_12__checked_shl (x: i8) (n: u32) : t_Option i8 =
  if n <. impl_12__BITS then Option_Some (x <<! n) <: t_Option i8 else Option_None <: t_Option i8

/// See [`std::primitive::i8::checked_shr`] (and similar for other integer types)
let impl_12__checked_shr (x: i8) (n: u32) : t_Option i8 =
  if n <. impl_12__BITS then Option_Some (x >>! n) <: t_Option i8 else Option_None <: t_Option i8

/// See [`std::primitive::i8::shl_exact`] (and similar for other signed integer types)
let impl_12__shl_exact (x: i8) (n: u32) : t_Option i8 =
  if
    (n <. (impl_12__leading_zeros x <: u32) || n <. (impl_12__leading_ones x <: u32)) &&
    n <. impl_12__BITS
  then Option_Some (x <<! n) <: t_Option i8
  else Option_None <: t_Option i8

/// See [`std::primitive::i8::shr_exact`] (and similar for other integer types)
let impl_12__shr_exact (x: i8) (n: u32) : t_Option i8 =
  if n <=. (impl_12__trailing_zeros x <: u32) && n <. impl_12__BITS
  then Option_Some (x >>! n) <: t_Option i8
  else Option_None <: t_Option i8

/// See [`std::primitive::i8::next_multiple_of`] (and similar for other signed integer types)
let impl_12__next_multiple_of (x y: i8)
    : Prims.Pure i8
      (requires
        (match impl_12__checked_next_multiple_of x y <: t_Option i8 with
          | Option_Some _ -> true
          | Option_None  -> false))
      (fun _ -> Prims.l_True) =
  match impl_12__checked_next_multiple_of x y <: t_Option i8 with
  | Option_Some result -> result
  | Option_None  -> Core_models.Panicking.Internal.panic #i8 ()

/// See [`std::primitive::u8::checked_add`] (and similar for other integer types)
let impl_13__checked_add (x y: i16) : t_Option i16 =
  let (result: i16), (overflowed: bool) = impl_13__overflowing_add x y in
  if overflowed then Option_None <: t_Option i16 else Option_Some result <: t_Option i16

/// See [`std::primitive::u8::checked_sub`] (and similar for other integer types)
let impl_13__checked_sub (x y: i16) : t_Option i16 =
  let (result: i16), (overflowed: bool) = impl_13__overflowing_sub x y in
  if overflowed then Option_None <: t_Option i16 else Option_Some result <: t_Option i16

/// See [`std::primitive::i8::checked_add_unsigned`] (and similar for other signed integer types)
let impl_13__checked_add_unsigned (x: i16) (y: u16) : t_Option i16 =
  let (result: i16), (overflowed: bool) = impl_13__overflowing_add x (cast (y <: u16) <: i16) in
  if overflowed =. (y >. (cast (impl_13__MAX <: i16) <: u16) <: bool)
  then Option_Some result <: t_Option i16
  else Option_None <: t_Option i16

/// See [`std::primitive::i8::checked_sub_unsigned`] (and similar for other signed integer types)
let impl_13__checked_sub_unsigned (x: i16) (y: u16) : t_Option i16 =
  let (result: i16), (overflowed: bool) = impl_13__overflowing_sub x (cast (y <: u16) <: i16) in
  if overflowed =. (y >. (cast (impl_13__MAX <: i16) <: u16) <: bool)
  then Option_Some result <: t_Option i16
  else Option_None <: t_Option i16

/// See [`std::primitive::u8::checked_mul`] (and similar for other integer types)
let impl_13__checked_mul (x y: i16) : t_Option i16 =
  let (result: i16), (overflowed: bool) = impl_13__overflowing_mul x y in
  if overflowed then Option_None <: t_Option i16 else Option_Some result <: t_Option i16

/// See [`std::primitive::i8::checked_div`] (and similar for other signed integer types)
let impl_13__checked_div (x y: i16) : t_Option i16 =
  if y =. mk_i16 0 || x =. impl_13__MIN && y =. mk_i16 (-1)
  then Option_None <: t_Option i16
  else Option_Some (x /! y) <: t_Option i16

/// See [`std::primitive::i8::checked_rem`] (and similar for other signed integer types)
let impl_13__checked_rem (x y: i16) : t_Option i16 =
  if y =. mk_i16 0 || x =. impl_13__MIN && y =. mk_i16 (-1)
  then Option_None <: t_Option i16
  else Option_Some (x %! y) <: t_Option i16

/// See [`std::primitive::i8::checked_ilog2`] (and similar for other integer types)
let impl_13__checked_ilog2 (x: i16) : t_Option u32 =
  if x <=. mk_i16 0
  then Option_None <: t_Option u32
  else Option_Some (impl_13__ilog2 x) <: t_Option u32

/// See [`std::primitive::i8::checked_neg`] (and similar for other integer types)
let impl_13__checked_neg (x: i16) : t_Option i16 =
  if x =. impl_13__MIN
  then Option_None <: t_Option i16
  else Option_Some (impl_13__wrapping_neg x) <: t_Option i16

/// See [`std::primitive::i8::checked_abs`] (and similar for other signed integer types)
let impl_13__checked_abs (x: i16) : t_Option i16 =
  if x <. mk_i16 0 then impl_13__checked_neg x else Option_Some x <: t_Option i16

/// See [`std::primitive::i8::checked_div_euclid`] (and similar for other signed integer types)
let impl_13__checked_div_euclid (x y: i16) : t_Option i16 =
  if y =. mk_i16 0 || x =. impl_13__MIN && y =. mk_i16 (-1)
  then Option_None <: t_Option i16
  else Option_Some (impl_13__div_euclid x y) <: t_Option i16

/// See [`std::primitive::i8::checked_rem_euclid`] (and similar for other signed integer types)
let impl_13__checked_rem_euclid (x y: i16) : t_Option i16 =
  if y =. mk_i16 0 || x =. impl_13__MIN && y =. mk_i16 (-1)
  then Option_None <: t_Option i16
  else Option_Some (impl_13__rem_euclid x y) <: t_Option i16

/// See [`std::primitive::i8::div_exact`] (and similar for other signed integer types)
let impl_13__div_exact (x y: i16)
    : Prims.Pure (t_Option i16)
      (requires y <>. mk_i16 0 && ~.((x =. impl_13__MIN <: bool) && (y =. mk_i16 (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  if (x %! y <: i16) <>. mk_i16 0
  then Option_None <: t_Option i16
  else Option_Some (x /! y) <: t_Option i16

/// See [`std::primitive::i8::checked_div_exact`] (and similar for other signed integer types)
let impl_13__checked_div_exact (x y: i16) : t_Option i16 =
  if y =. mk_i16 0 || x =. impl_13__MIN && y =. mk_i16 (-1) || (x %! y <: i16) <>. mk_i16 0
  then Option_None <: t_Option i16
  else Option_Some (x /! y) <: t_Option i16

/// See [`std::primitive::i8::checked_next_multiple_of`] (and similar for other signed integer types)
let impl_13__checked_next_multiple_of (x y: i16) : t_Option i16 =
  if y =. mk_i16 (-1)
  then Option_Some x <: t_Option i16
  else
    if y =. mk_i16 0
    then Option_None <: t_Option i16
    else
      let r:i16 = x %! y in
      let m:i16 =
        if r >. mk_i16 0 && y <. mk_i16 0 || r <. mk_i16 0 && y >. mk_i16 0
        then impl_13__wrapping_add r y
        else r
      in
      if m =. mk_i16 0
      then Option_Some x <: t_Option i16
      else impl_13__checked_add x (impl_13__wrapping_sub y m <: i16)

/// See [`std::primitive::i8::highest_one`] (and similar for other signed integer types)
assume
val impl_13__highest_one': x: i16 -> t_Option u32

unfold
let impl_13__highest_one = impl_13__highest_one'

/// See [`std::primitive::i8::lowest_one`] (and similar for other integer types)
let impl_13__lowest_one (x: i16) : t_Option u32 =
  if x =. mk_i16 0
  then Option_None <: t_Option u32
  else Option_Some (impl_13__trailing_zeros x) <: t_Option u32

/// See [`std::primitive::i8::checked_shl`] (and similar for other integer types)
let impl_13__checked_shl (x: i16) (n: u32) : t_Option i16 =
  if n <. impl_13__BITS then Option_Some (x <<! n) <: t_Option i16 else Option_None <: t_Option i16

/// See [`std::primitive::i8::checked_shr`] (and similar for other integer types)
let impl_13__checked_shr (x: i16) (n: u32) : t_Option i16 =
  if n <. impl_13__BITS then Option_Some (x >>! n) <: t_Option i16 else Option_None <: t_Option i16

/// See [`std::primitive::i8::shl_exact`] (and similar for other signed integer types)
let impl_13__shl_exact (x: i16) (n: u32) : t_Option i16 =
  if
    (n <. (impl_13__leading_zeros x <: u32) || n <. (impl_13__leading_ones x <: u32)) &&
    n <. impl_13__BITS
  then Option_Some (x <<! n) <: t_Option i16
  else Option_None <: t_Option i16

/// See [`std::primitive::i8::shr_exact`] (and similar for other integer types)
let impl_13__shr_exact (x: i16) (n: u32) : t_Option i16 =
  if n <=. (impl_13__trailing_zeros x <: u32) && n <. impl_13__BITS
  then Option_Some (x >>! n) <: t_Option i16
  else Option_None <: t_Option i16

/// See [`std::primitive::i8::next_multiple_of`] (and similar for other signed integer types)
let impl_13__next_multiple_of (x y: i16)
    : Prims.Pure i16
      (requires
        (match impl_13__checked_next_multiple_of x y <: t_Option i16 with
          | Option_Some _ -> true
          | Option_None  -> false))
      (fun _ -> Prims.l_True) =
  match impl_13__checked_next_multiple_of x y <: t_Option i16 with
  | Option_Some result -> result
  | Option_None  -> Core_models.Panicking.Internal.panic #i16 ()

/// See [`std::primitive::u8::checked_add`] (and similar for other integer types)
let impl_14__checked_add (x y: i32) : t_Option i32 =
  let (result: i32), (overflowed: bool) = impl_14__overflowing_add x y in
  if overflowed then Option_None <: t_Option i32 else Option_Some result <: t_Option i32

/// See [`std::primitive::u8::checked_sub`] (and similar for other integer types)
let impl_14__checked_sub (x y: i32) : t_Option i32 =
  let (result: i32), (overflowed: bool) = impl_14__overflowing_sub x y in
  if overflowed then Option_None <: t_Option i32 else Option_Some result <: t_Option i32

/// See [`std::primitive::i8::checked_add_unsigned`] (and similar for other signed integer types)
let impl_14__checked_add_unsigned (x: i32) (y: u32) : t_Option i32 =
  let (result: i32), (overflowed: bool) = impl_14__overflowing_add x (cast (y <: u32) <: i32) in
  if overflowed =. (y >. (cast (impl_14__MAX <: i32) <: u32) <: bool)
  then Option_Some result <: t_Option i32
  else Option_None <: t_Option i32

/// See [`std::primitive::i8::checked_sub_unsigned`] (and similar for other signed integer types)
let impl_14__checked_sub_unsigned (x: i32) (y: u32) : t_Option i32 =
  let (result: i32), (overflowed: bool) = impl_14__overflowing_sub x (cast (y <: u32) <: i32) in
  if overflowed =. (y >. (cast (impl_14__MAX <: i32) <: u32) <: bool)
  then Option_Some result <: t_Option i32
  else Option_None <: t_Option i32

/// See [`std::primitive::u8::checked_mul`] (and similar for other integer types)
let impl_14__checked_mul (x y: i32) : t_Option i32 =
  let (result: i32), (overflowed: bool) = impl_14__overflowing_mul x y in
  if overflowed then Option_None <: t_Option i32 else Option_Some result <: t_Option i32

/// See [`std::primitive::i8::checked_div`] (and similar for other signed integer types)
let impl_14__checked_div (x y: i32) : t_Option i32 =
  if y =. mk_i32 0 || x =. impl_14__MIN && y =. mk_i32 (-1)
  then Option_None <: t_Option i32
  else Option_Some (x /! y) <: t_Option i32

/// See [`std::primitive::i8::checked_rem`] (and similar for other signed integer types)
let impl_14__checked_rem (x y: i32) : t_Option i32 =
  if y =. mk_i32 0 || x =. impl_14__MIN && y =. mk_i32 (-1)
  then Option_None <: t_Option i32
  else Option_Some (x %! y) <: t_Option i32

/// See [`std::primitive::i8::checked_ilog2`] (and similar for other integer types)
let impl_14__checked_ilog2 (x: i32) : t_Option u32 =
  if x <=. mk_i32 0
  then Option_None <: t_Option u32
  else Option_Some (impl_14__ilog2 x) <: t_Option u32

/// See [`std::primitive::i8::checked_neg`] (and similar for other integer types)
let impl_14__checked_neg (x: i32) : t_Option i32 =
  if x =. impl_14__MIN
  then Option_None <: t_Option i32
  else Option_Some (impl_14__wrapping_neg x) <: t_Option i32

/// See [`std::primitive::i8::checked_abs`] (and similar for other signed integer types)
let impl_14__checked_abs (x: i32) : t_Option i32 =
  if x <. mk_i32 0 then impl_14__checked_neg x else Option_Some x <: t_Option i32

/// See [`std::primitive::i8::checked_div_euclid`] (and similar for other signed integer types)
let impl_14__checked_div_euclid (x y: i32) : t_Option i32 =
  if y =. mk_i32 0 || x =. impl_14__MIN && y =. mk_i32 (-1)
  then Option_None <: t_Option i32
  else Option_Some (impl_14__div_euclid x y) <: t_Option i32

/// See [`std::primitive::i8::checked_rem_euclid`] (and similar for other signed integer types)
let impl_14__checked_rem_euclid (x y: i32) : t_Option i32 =
  if y =. mk_i32 0 || x =. impl_14__MIN && y =. mk_i32 (-1)
  then Option_None <: t_Option i32
  else Option_Some (impl_14__rem_euclid x y) <: t_Option i32

/// See [`std::primitive::i8::div_exact`] (and similar for other signed integer types)
let impl_14__div_exact (x y: i32)
    : Prims.Pure (t_Option i32)
      (requires y <>. mk_i32 0 && ~.((x =. impl_14__MIN <: bool) && (y =. mk_i32 (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  if (x %! y <: i32) <>. mk_i32 0
  then Option_None <: t_Option i32
  else Option_Some (x /! y) <: t_Option i32

/// See [`std::primitive::i8::checked_div_exact`] (and similar for other signed integer types)
let impl_14__checked_div_exact (x y: i32) : t_Option i32 =
  if y =. mk_i32 0 || x =. impl_14__MIN && y =. mk_i32 (-1) || (x %! y <: i32) <>. mk_i32 0
  then Option_None <: t_Option i32
  else Option_Some (x /! y) <: t_Option i32

/// See [`std::primitive::i8::checked_next_multiple_of`] (and similar for other signed integer types)
let impl_14__checked_next_multiple_of (x y: i32) : t_Option i32 =
  if y =. mk_i32 (-1)
  then Option_Some x <: t_Option i32
  else
    if y =. mk_i32 0
    then Option_None <: t_Option i32
    else
      let r:i32 = x %! y in
      let m:i32 =
        if r >. mk_i32 0 && y <. mk_i32 0 || r <. mk_i32 0 && y >. mk_i32 0
        then impl_14__wrapping_add r y
        else r
      in
      if m =. mk_i32 0
      then Option_Some x <: t_Option i32
      else impl_14__checked_add x (impl_14__wrapping_sub y m <: i32)

/// See [`std::primitive::i8::highest_one`] (and similar for other signed integer types)
assume
val impl_14__highest_one': x: i32 -> t_Option u32

unfold
let impl_14__highest_one = impl_14__highest_one'

/// See [`std::primitive::i8::lowest_one`] (and similar for other integer types)
let impl_14__lowest_one (x: i32) : t_Option u32 =
  if x =. mk_i32 0
  then Option_None <: t_Option u32
  else Option_Some (impl_14__trailing_zeros x) <: t_Option u32

/// See [`std::primitive::i8::checked_shl`] (and similar for other integer types)
let impl_14__checked_shl (x: i32) (n: u32) : t_Option i32 =
  if n <. impl_14__BITS then Option_Some (x <<! n) <: t_Option i32 else Option_None <: t_Option i32

/// See [`std::primitive::i8::checked_shr`] (and similar for other integer types)
let impl_14__checked_shr (x: i32) (n: u32) : t_Option i32 =
  if n <. impl_14__BITS then Option_Some (x >>! n) <: t_Option i32 else Option_None <: t_Option i32

/// See [`std::primitive::i8::shl_exact`] (and similar for other signed integer types)
let impl_14__shl_exact (x: i32) (n: u32) : t_Option i32 =
  if
    (n <. (impl_14__leading_zeros x <: u32) || n <. (impl_14__leading_ones x <: u32)) &&
    n <. impl_14__BITS
  then Option_Some (x <<! n) <: t_Option i32
  else Option_None <: t_Option i32

/// See [`std::primitive::i8::shr_exact`] (and similar for other integer types)
let impl_14__shr_exact (x: i32) (n: u32) : t_Option i32 =
  if n <=. (impl_14__trailing_zeros x <: u32) && n <. impl_14__BITS
  then Option_Some (x >>! n) <: t_Option i32
  else Option_None <: t_Option i32

/// See [`std::primitive::i8::next_multiple_of`] (and similar for other signed integer types)
let impl_14__next_multiple_of (x y: i32)
    : Prims.Pure i32
      (requires
        (match impl_14__checked_next_multiple_of x y <: t_Option i32 with
          | Option_Some _ -> true
          | Option_None  -> false))
      (fun _ -> Prims.l_True) =
  match impl_14__checked_next_multiple_of x y <: t_Option i32 with
  | Option_Some result -> result
  | Option_None  -> Core_models.Panicking.Internal.panic #i32 ()

/// See [`std::primitive::u8::checked_add`] (and similar for other integer types)
let impl_15__checked_add (x y: i64) : t_Option i64 =
  let (result: i64), (overflowed: bool) = impl_15__overflowing_add x y in
  if overflowed then Option_None <: t_Option i64 else Option_Some result <: t_Option i64

/// See [`std::primitive::u8::checked_sub`] (and similar for other integer types)
let impl_15__checked_sub (x y: i64) : t_Option i64 =
  let (result: i64), (overflowed: bool) = impl_15__overflowing_sub x y in
  if overflowed then Option_None <: t_Option i64 else Option_Some result <: t_Option i64

/// See [`std::primitive::i8::checked_add_unsigned`] (and similar for other signed integer types)
let impl_15__checked_add_unsigned (x: i64) (y: u64) : t_Option i64 =
  let (result: i64), (overflowed: bool) = impl_15__overflowing_add x (cast (y <: u64) <: i64) in
  if overflowed =. (y >. (cast (impl_15__MAX <: i64) <: u64) <: bool)
  then Option_Some result <: t_Option i64
  else Option_None <: t_Option i64

/// See [`std::primitive::i8::checked_sub_unsigned`] (and similar for other signed integer types)
let impl_15__checked_sub_unsigned (x: i64) (y: u64) : t_Option i64 =
  let (result: i64), (overflowed: bool) = impl_15__overflowing_sub x (cast (y <: u64) <: i64) in
  if overflowed =. (y >. (cast (impl_15__MAX <: i64) <: u64) <: bool)
  then Option_Some result <: t_Option i64
  else Option_None <: t_Option i64

/// See [`std::primitive::u8::checked_mul`] (and similar for other integer types)
let impl_15__checked_mul (x y: i64) : t_Option i64 =
  let (result: i64), (overflowed: bool) = impl_15__overflowing_mul x y in
  if overflowed then Option_None <: t_Option i64 else Option_Some result <: t_Option i64

/// See [`std::primitive::i8::checked_div`] (and similar for other signed integer types)
let impl_15__checked_div (x y: i64) : t_Option i64 =
  if y =. mk_i64 0 || x =. impl_15__MIN && y =. mk_i64 (-1)
  then Option_None <: t_Option i64
  else Option_Some (x /! y) <: t_Option i64

/// See [`std::primitive::i8::checked_rem`] (and similar for other signed integer types)
let impl_15__checked_rem (x y: i64) : t_Option i64 =
  if y =. mk_i64 0 || x =. impl_15__MIN && y =. mk_i64 (-1)
  then Option_None <: t_Option i64
  else Option_Some (x %! y) <: t_Option i64

/// See [`std::primitive::i8::checked_ilog2`] (and similar for other integer types)
let impl_15__checked_ilog2 (x: i64) : t_Option u32 =
  if x <=. mk_i64 0
  then Option_None <: t_Option u32
  else Option_Some (impl_15__ilog2 x) <: t_Option u32

/// See [`std::primitive::i8::checked_neg`] (and similar for other integer types)
let impl_15__checked_neg (x: i64) : t_Option i64 =
  if x =. impl_15__MIN
  then Option_None <: t_Option i64
  else Option_Some (impl_15__wrapping_neg x) <: t_Option i64

/// See [`std::primitive::i8::checked_abs`] (and similar for other signed integer types)
let impl_15__checked_abs (x: i64) : t_Option i64 =
  if x <. mk_i64 0 then impl_15__checked_neg x else Option_Some x <: t_Option i64

/// See [`std::primitive::i8::checked_div_euclid`] (and similar for other signed integer types)
let impl_15__checked_div_euclid (x y: i64) : t_Option i64 =
  if y =. mk_i64 0 || x =. impl_15__MIN && y =. mk_i64 (-1)
  then Option_None <: t_Option i64
  else Option_Some (impl_15__div_euclid x y) <: t_Option i64

/// See [`std::primitive::i8::checked_rem_euclid`] (and similar for other signed integer types)
let impl_15__checked_rem_euclid (x y: i64) : t_Option i64 =
  if y =. mk_i64 0 || x =. impl_15__MIN && y =. mk_i64 (-1)
  then Option_None <: t_Option i64
  else Option_Some (impl_15__rem_euclid x y) <: t_Option i64

/// See [`std::primitive::i8::div_exact`] (and similar for other signed integer types)
let impl_15__div_exact (x y: i64)
    : Prims.Pure (t_Option i64)
      (requires y <>. mk_i64 0 && ~.((x =. impl_15__MIN <: bool) && (y =. mk_i64 (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  if (x %! y <: i64) <>. mk_i64 0
  then Option_None <: t_Option i64
  else Option_Some (x /! y) <: t_Option i64

/// See [`std::primitive::i8::checked_div_exact`] (and similar for other signed integer types)
let impl_15__checked_div_exact (x y: i64) : t_Option i64 =
  if y =. mk_i64 0 || x =. impl_15__MIN && y =. mk_i64 (-1) || (x %! y <: i64) <>. mk_i64 0
  then Option_None <: t_Option i64
  else Option_Some (x /! y) <: t_Option i64

/// See [`std::primitive::i8::checked_next_multiple_of`] (and similar for other signed integer types)
let impl_15__checked_next_multiple_of (x y: i64) : t_Option i64 =
  if y =. mk_i64 (-1)
  then Option_Some x <: t_Option i64
  else
    if y =. mk_i64 0
    then Option_None <: t_Option i64
    else
      let r:i64 = x %! y in
      let m:i64 =
        if r >. mk_i64 0 && y <. mk_i64 0 || r <. mk_i64 0 && y >. mk_i64 0
        then impl_15__wrapping_add r y
        else r
      in
      if m =. mk_i64 0
      then Option_Some x <: t_Option i64
      else impl_15__checked_add x (impl_15__wrapping_sub y m <: i64)

/// See [`std::primitive::i8::highest_one`] (and similar for other signed integer types)
assume
val impl_15__highest_one': x: i64 -> t_Option u32

unfold
let impl_15__highest_one = impl_15__highest_one'

/// See [`std::primitive::i8::lowest_one`] (and similar for other integer types)
let impl_15__lowest_one (x: i64) : t_Option u32 =
  if x =. mk_i64 0
  then Option_None <: t_Option u32
  else Option_Some (impl_15__trailing_zeros x) <: t_Option u32

/// See [`std::primitive::i8::checked_shl`] (and similar for other integer types)
let impl_15__checked_shl (x: i64) (n: u32) : t_Option i64 =
  if n <. impl_15__BITS then Option_Some (x <<! n) <: t_Option i64 else Option_None <: t_Option i64

/// See [`std::primitive::i8::checked_shr`] (and similar for other integer types)
let impl_15__checked_shr (x: i64) (n: u32) : t_Option i64 =
  if n <. impl_15__BITS then Option_Some (x >>! n) <: t_Option i64 else Option_None <: t_Option i64

/// See [`std::primitive::i8::shl_exact`] (and similar for other signed integer types)
let impl_15__shl_exact (x: i64) (n: u32) : t_Option i64 =
  if
    (n <. (impl_15__leading_zeros x <: u32) || n <. (impl_15__leading_ones x <: u32)) &&
    n <. impl_15__BITS
  then Option_Some (x <<! n) <: t_Option i64
  else Option_None <: t_Option i64

/// See [`std::primitive::i8::shr_exact`] (and similar for other integer types)
let impl_15__shr_exact (x: i64) (n: u32) : t_Option i64 =
  if n <=. (impl_15__trailing_zeros x <: u32) && n <. impl_15__BITS
  then Option_Some (x >>! n) <: t_Option i64
  else Option_None <: t_Option i64

/// See [`std::primitive::i8::next_multiple_of`] (and similar for other signed integer types)
let impl_15__next_multiple_of (x y: i64)
    : Prims.Pure i64
      (requires
        (match impl_15__checked_next_multiple_of x y <: t_Option i64 with
          | Option_Some _ -> true
          | Option_None  -> false))
      (fun _ -> Prims.l_True) =
  match impl_15__checked_next_multiple_of x y <: t_Option i64 with
  | Option_Some result -> result
  | Option_None  -> Core_models.Panicking.Internal.panic #i64 ()

/// See [`std::primitive::u8::checked_add`] (and similar for other integer types)
let impl_16__checked_add (x y: i128) : t_Option i128 =
  let (result: i128), (overflowed: bool) = impl_16__overflowing_add x y in
  if overflowed then Option_None <: t_Option i128 else Option_Some result <: t_Option i128

/// See [`std::primitive::u8::checked_sub`] (and similar for other integer types)
let impl_16__checked_sub (x y: i128) : t_Option i128 =
  let (result: i128), (overflowed: bool) = impl_16__overflowing_sub x y in
  if overflowed then Option_None <: t_Option i128 else Option_Some result <: t_Option i128

/// See [`std::primitive::i8::checked_add_unsigned`] (and similar for other signed integer types)
let impl_16__checked_add_unsigned (x: i128) (y: u128) : t_Option i128 =
  let (result: i128), (overflowed: bool) = impl_16__overflowing_add x (cast (y <: u128) <: i128) in
  if overflowed =. (y >. (cast (impl_16__MAX <: i128) <: u128) <: bool)
  then Option_Some result <: t_Option i128
  else Option_None <: t_Option i128

/// See [`std::primitive::i8::checked_sub_unsigned`] (and similar for other signed integer types)
let impl_16__checked_sub_unsigned (x: i128) (y: u128) : t_Option i128 =
  let (result: i128), (overflowed: bool) = impl_16__overflowing_sub x (cast (y <: u128) <: i128) in
  if overflowed =. (y >. (cast (impl_16__MAX <: i128) <: u128) <: bool)
  then Option_Some result <: t_Option i128
  else Option_None <: t_Option i128

/// See [`std::primitive::u8::checked_mul`] (and similar for other integer types)
let impl_16__checked_mul (x y: i128) : t_Option i128 =
  let (result: i128), (overflowed: bool) = impl_16__overflowing_mul x y in
  if overflowed then Option_None <: t_Option i128 else Option_Some result <: t_Option i128

/// See [`std::primitive::i8::checked_div`] (and similar for other signed integer types)
let impl_16__checked_div (x y: i128) : t_Option i128 =
  if y =. mk_i128 0 || x =. impl_16__MIN && y =. mk_i128 (-1)
  then Option_None <: t_Option i128
  else Option_Some (x /! y) <: t_Option i128

/// See [`std::primitive::i8::checked_rem`] (and similar for other signed integer types)
let impl_16__checked_rem (x y: i128) : t_Option i128 =
  if y =. mk_i128 0 || x =. impl_16__MIN && y =. mk_i128 (-1)
  then Option_None <: t_Option i128
  else Option_Some (x %! y) <: t_Option i128

/// See [`std::primitive::i8::checked_ilog2`] (and similar for other integer types)
let impl_16__checked_ilog2 (x: i128) : t_Option u32 =
  if x <=. mk_i128 0
  then Option_None <: t_Option u32
  else Option_Some (impl_16__ilog2 x) <: t_Option u32

/// See [`std::primitive::i8::checked_neg`] (and similar for other integer types)
let impl_16__checked_neg (x: i128) : t_Option i128 =
  if x =. impl_16__MIN
  then Option_None <: t_Option i128
  else Option_Some (impl_16__wrapping_neg x) <: t_Option i128

/// See [`std::primitive::i8::checked_abs`] (and similar for other signed integer types)
let impl_16__checked_abs (x: i128) : t_Option i128 =
  if x <. mk_i128 0 then impl_16__checked_neg x else Option_Some x <: t_Option i128

/// See [`std::primitive::i8::checked_div_euclid`] (and similar for other signed integer types)
let impl_16__checked_div_euclid (x y: i128) : t_Option i128 =
  if y =. mk_i128 0 || x =. impl_16__MIN && y =. mk_i128 (-1)
  then Option_None <: t_Option i128
  else Option_Some (impl_16__div_euclid x y) <: t_Option i128

/// See [`std::primitive::i8::checked_rem_euclid`] (and similar for other signed integer types)
let impl_16__checked_rem_euclid (x y: i128) : t_Option i128 =
  if y =. mk_i128 0 || x =. impl_16__MIN && y =. mk_i128 (-1)
  then Option_None <: t_Option i128
  else Option_Some (impl_16__rem_euclid x y) <: t_Option i128

/// See [`std::primitive::i8::div_exact`] (and similar for other signed integer types)
let impl_16__div_exact (x y: i128)
    : Prims.Pure (t_Option i128)
      (requires y <>. mk_i128 0 && ~.((x =. impl_16__MIN <: bool) && (y =. mk_i128 (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  if (x %! y <: i128) <>. mk_i128 0
  then Option_None <: t_Option i128
  else Option_Some (x /! y) <: t_Option i128

/// See [`std::primitive::i8::checked_div_exact`] (and similar for other signed integer types)
let impl_16__checked_div_exact (x y: i128) : t_Option i128 =
  if y =. mk_i128 0 || x =. impl_16__MIN && y =. mk_i128 (-1) || (x %! y <: i128) <>. mk_i128 0
  then Option_None <: t_Option i128
  else Option_Some (x /! y) <: t_Option i128

/// See [`std::primitive::i8::checked_next_multiple_of`] (and similar for other signed integer types)
let impl_16__checked_next_multiple_of (x y: i128) : t_Option i128 =
  if y =. mk_i128 (-1)
  then Option_Some x <: t_Option i128
  else
    if y =. mk_i128 0
    then Option_None <: t_Option i128
    else
      let r:i128 = x %! y in
      let m:i128 =
        if r >. mk_i128 0 && y <. mk_i128 0 || r <. mk_i128 0 && y >. mk_i128 0
        then impl_16__wrapping_add r y
        else r
      in
      if m =. mk_i128 0
      then Option_Some x <: t_Option i128
      else impl_16__checked_add x (impl_16__wrapping_sub y m <: i128)

/// See [`std::primitive::i8::highest_one`] (and similar for other signed integer types)
assume
val impl_16__highest_one': x: i128 -> t_Option u32

unfold
let impl_16__highest_one = impl_16__highest_one'

/// See [`std::primitive::i8::lowest_one`] (and similar for other integer types)
let impl_16__lowest_one (x: i128) : t_Option u32 =
  if x =. mk_i128 0
  then Option_None <: t_Option u32
  else Option_Some (impl_16__trailing_zeros x) <: t_Option u32

/// See [`std::primitive::i8::checked_shl`] (and similar for other integer types)
let impl_16__checked_shl (x: i128) (n: u32) : t_Option i128 =
  if n <. impl_16__BITS
  then Option_Some (x <<! n) <: t_Option i128
  else Option_None <: t_Option i128

/// See [`std::primitive::i8::checked_shr`] (and similar for other integer types)
let impl_16__checked_shr (x: i128) (n: u32) : t_Option i128 =
  if n <. impl_16__BITS
  then Option_Some (x >>! n) <: t_Option i128
  else Option_None <: t_Option i128

/// See [`std::primitive::i8::shl_exact`] (and similar for other signed integer types)
let impl_16__shl_exact (x: i128) (n: u32) : t_Option i128 =
  if
    (n <. (impl_16__leading_zeros x <: u32) || n <. (impl_16__leading_ones x <: u32)) &&
    n <. impl_16__BITS
  then Option_Some (x <<! n) <: t_Option i128
  else Option_None <: t_Option i128

/// See [`std::primitive::i8::shr_exact`] (and similar for other integer types)
let impl_16__shr_exact (x: i128) (n: u32) : t_Option i128 =
  if n <=. (impl_16__trailing_zeros x <: u32) && n <. impl_16__BITS
  then Option_Some (x >>! n) <: t_Option i128
  else Option_None <: t_Option i128

/// See [`std::primitive::i8::next_multiple_of`] (and similar for other signed integer types)
let impl_16__next_multiple_of (x y: i128)
    : Prims.Pure i128
      (requires
        (match impl_16__checked_next_multiple_of x y <: t_Option i128 with
          | Option_Some _ -> true
          | Option_None  -> false))
      (fun _ -> Prims.l_True) =
  match impl_16__checked_next_multiple_of x y <: t_Option i128 with
  | Option_Some result -> result
  | Option_None  -> Core_models.Panicking.Internal.panic #i128 ()

/// See [`std::primitive::u8::checked_add`] (and similar for other integer types)
let impl_17__checked_add (x y: isize) : t_Option isize =
  let (result: isize), (overflowed: bool) = impl_17__overflowing_add x y in
  if overflowed then Option_None <: t_Option isize else Option_Some result <: t_Option isize

/// See [`std::primitive::u8::checked_sub`] (and similar for other integer types)
let impl_17__checked_sub (x y: isize) : t_Option isize =
  let (result: isize), (overflowed: bool) = impl_17__overflowing_sub x y in
  if overflowed then Option_None <: t_Option isize else Option_Some result <: t_Option isize

/// See [`std::primitive::i8::checked_add_unsigned`] (and similar for other signed integer types)
let impl_17__checked_add_unsigned (x: isize) (y: usize) : t_Option isize =
  let (result: isize), (overflowed: bool) =
    impl_17__overflowing_add x (cast (y <: usize) <: isize)
  in
  if overflowed =. (y >. (cast (impl_17__MAX <: isize) <: usize) <: bool)
  then Option_Some result <: t_Option isize
  else Option_None <: t_Option isize

/// See [`std::primitive::i8::checked_sub_unsigned`] (and similar for other signed integer types)
let impl_17__checked_sub_unsigned (x: isize) (y: usize) : t_Option isize =
  let (result: isize), (overflowed: bool) =
    impl_17__overflowing_sub x (cast (y <: usize) <: isize)
  in
  if overflowed =. (y >. (cast (impl_17__MAX <: isize) <: usize) <: bool)
  then Option_Some result <: t_Option isize
  else Option_None <: t_Option isize

/// See [`std::primitive::u8::checked_mul`] (and similar for other integer types)
let impl_17__checked_mul (x y: isize) : t_Option isize =
  let (result: isize), (overflowed: bool) = impl_17__overflowing_mul x y in
  if overflowed then Option_None <: t_Option isize else Option_Some result <: t_Option isize

/// See [`std::primitive::i8::checked_div`] (and similar for other signed integer types)
let impl_17__checked_div (x y: isize) : t_Option isize =
  if y =. mk_isize 0 || x =. impl_17__MIN && y =. mk_isize (-1)
  then Option_None <: t_Option isize
  else Option_Some (x /! y) <: t_Option isize

/// See [`std::primitive::i8::checked_rem`] (and similar for other signed integer types)
let impl_17__checked_rem (x y: isize) : t_Option isize =
  if y =. mk_isize 0 || x =. impl_17__MIN && y =. mk_isize (-1)
  then Option_None <: t_Option isize
  else Option_Some (x %! y) <: t_Option isize

/// See [`std::primitive::i8::checked_ilog2`] (and similar for other integer types)
let impl_17__checked_ilog2 (x: isize) : t_Option u32 =
  if x <=. mk_isize 0
  then Option_None <: t_Option u32
  else Option_Some (impl_17__ilog2 x) <: t_Option u32

/// See [`std::primitive::i8::checked_neg`] (and similar for other integer types)
let impl_17__checked_neg (x: isize) : t_Option isize =
  if x =. impl_17__MIN
  then Option_None <: t_Option isize
  else Option_Some (impl_17__wrapping_neg x) <: t_Option isize

/// See [`std::primitive::i8::checked_abs`] (and similar for other signed integer types)
let impl_17__checked_abs (x: isize) : t_Option isize =
  if x <. mk_isize 0 then impl_17__checked_neg x else Option_Some x <: t_Option isize

/// See [`std::primitive::i8::checked_div_euclid`] (and similar for other signed integer types)
let impl_17__checked_div_euclid (x y: isize) : t_Option isize =
  if y =. mk_isize 0 || x =. impl_17__MIN && y =. mk_isize (-1)
  then Option_None <: t_Option isize
  else Option_Some (impl_17__div_euclid x y) <: t_Option isize

/// See [`std::primitive::i8::checked_rem_euclid`] (and similar for other signed integer types)
let impl_17__checked_rem_euclid (x y: isize) : t_Option isize =
  if y =. mk_isize 0 || x =. impl_17__MIN && y =. mk_isize (-1)
  then Option_None <: t_Option isize
  else Option_Some (impl_17__rem_euclid x y) <: t_Option isize

/// See [`std::primitive::i8::div_exact`] (and similar for other signed integer types)
let impl_17__div_exact (x y: isize)
    : Prims.Pure (t_Option isize)
      (requires y <>. mk_isize 0 && ~.((x =. impl_17__MIN <: bool) && (y =. mk_isize (-1) <: bool)))
      (fun _ -> Prims.l_True) =
  if (x %! y <: isize) <>. mk_isize 0
  then Option_None <: t_Option isize
  else Option_Some (x /! y) <: t_Option isize

/// See [`std::primitive::i8::checked_div_exact`] (and similar for other signed integer types)
let impl_17__checked_div_exact (x y: isize) : t_Option isize =
  if y =. mk_isize 0 || x =. impl_17__MIN && y =. mk_isize (-1) || (x %! y <: isize) <>. mk_isize 0
  then Option_None <: t_Option isize
  else Option_Some (x /! y) <: t_Option isize

/// See [`std::primitive::i8::checked_next_multiple_of`] (and similar for other signed integer types)
let impl_17__checked_next_multiple_of (x y: isize) : t_Option isize =
  if y =. mk_isize (-1)
  then Option_Some x <: t_Option isize
  else
    if y =. mk_isize 0
    then Option_None <: t_Option isize
    else
      let r:isize = x %! y in
      let m:isize =
        if r >. mk_isize 0 && y <. mk_isize 0 || r <. mk_isize 0 && y >. mk_isize 0
        then impl_17__wrapping_add r y
        else r
      in
      if m =. mk_isize 0
      then Option_Some x <: t_Option isize
      else impl_17__checked_add x (impl_17__wrapping_sub y m <: isize)

/// See [`std::primitive::i8::highest_one`] (and similar for other signed integer types)
assume
val impl_17__highest_one': x: isize -> t_Option u32

unfold
let impl_17__highest_one = impl_17__highest_one'

/// See [`std::primitive::i8::lowest_one`] (and similar for other integer types)
let impl_17__lowest_one (x: isize) : t_Option u32 =
  if x =. mk_isize 0
  then Option_None <: t_Option u32
  else Option_Some (impl_17__trailing_zeros x) <: t_Option u32

/// See [`std::primitive::i8::checked_shl`] (and similar for other integer types)
let impl_17__checked_shl (x: isize) (n: u32) : t_Option isize =
  if n <. impl_17__BITS
  then Option_Some (x <<! n) <: t_Option isize
  else Option_None <: t_Option isize

/// See [`std::primitive::i8::checked_shr`] (and similar for other integer types)
let impl_17__checked_shr (x: isize) (n: u32) : t_Option isize =
  if n <. impl_17__BITS
  then Option_Some (x >>! n) <: t_Option isize
  else Option_None <: t_Option isize

/// See [`std::primitive::i8::shl_exact`] (and similar for other signed integer types)
let impl_17__shl_exact (x: isize) (n: u32) : t_Option isize =
  if
    (n <. (impl_17__leading_zeros x <: u32) || n <. (impl_17__leading_ones x <: u32)) &&
    n <. impl_17__BITS
  then Option_Some (x <<! n) <: t_Option isize
  else Option_None <: t_Option isize

/// See [`std::primitive::i8::shr_exact`] (and similar for other integer types)
let impl_17__shr_exact (x: isize) (n: u32) : t_Option isize =
  if n <=. (impl_17__trailing_zeros x <: u32) && n <. impl_17__BITS
  then Option_Some (x >>! n) <: t_Option isize
  else Option_None <: t_Option isize

/// See [`std::primitive::i8::next_multiple_of`] (and similar for other signed integer types)
let impl_17__next_multiple_of (x y: isize)
    : Prims.Pure isize
      (requires
        (match impl_17__checked_next_multiple_of x y <: t_Option isize with
          | Option_Some _ -> true
          | Option_None  -> false))
      (fun _ -> Prims.l_True) =
  match impl_17__checked_next_multiple_of x y <: t_Option isize with
  | Option_Some result -> result
  | Option_None  -> Core_models.Panicking.Internal.panic #isize ()

/// See [`std::ops::ControlFlow::break_value`]
let impl__break_value (#v_B #v_C: Type0) (self: t_ControlFlow v_B v_C) : t_Option v_B =
  match self <: t_ControlFlow v_B v_C with
  | ControlFlow_Continue _ -> Option_None <: t_Option v_B
  | ControlFlow_Break x -> Option_Some x <: t_Option v_B

/// See [`std::ops::ControlFlow::continue_value`]
let impl__continue_value (#v_B #v_C: Type0) (self: t_ControlFlow v_B v_C) : t_Option v_C =
  match self <: t_ControlFlow v_B v_C with
  | ControlFlow_Continue x -> Option_Some x <: t_Option v_C
  | ControlFlow_Break _ -> Option_None <: t_Option v_C

/// See [`std::option::Option::is_some_and`]
let impl__is_some_and
      (#v_T #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_T)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == bool})
      (self: t_Option v_T)
      (f: v_F)
    : bool =
  match self <: t_Option v_T with
  | Option_None  -> false
  | Option_Some x ->
    Core_models.Ops.Function.f_call_once #v_F #v_T #FStar.Tactics.Typeclasses.solve f (x <: v_T)

/// See [`std::option::Option::is_none_or`]
let impl__is_none_or
      (#v_T #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_T)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == bool})
      (self: t_Option v_T)
      (f: v_F)
    : bool =
  match self <: t_Option v_T with
  | Option_None  -> true
  | Option_Some x ->
    Core_models.Ops.Function.f_call_once #v_F #v_T #FStar.Tactics.Typeclasses.solve f (x <: v_T)

/// See [`std::option::Option::as_ref`]
let impl__as_ref__from__option (#v_T: Type0) (self: t_Option v_T) : t_Option v_T =
  match self <: t_Option v_T with
  | Option_Some x -> Option_Some x <: t_Option v_T
  | Option_None  -> Option_None <: t_Option v_T

/// See [`std::option::Option::unwrap_or`]
let impl__unwrap_or (#v_T: Type0) (self: t_Option v_T) (v_default: v_T) : v_T =
  match self <: t_Option v_T with
  | Option_Some x -> x
  | Option_None  -> v_default

/// See [`std::option::Option::unwrap_or_else`]
let impl__unwrap_or_else
      (#v_T #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Core_models.Ops.Function.t_FnOnce v_F Prims.unit)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_T})
      (self: t_Option v_T)
      (f: v_F)
    : v_T =
  match self <: t_Option v_T with
  | Option_Some x -> x
  | Option_None  ->
    Core_models.Ops.Function.f_call_once #v_F
      #Prims.unit
      #FStar.Tactics.Typeclasses.solve
      f
      (() <: Prims.unit)

/// See [`std::option::Option::unwrap_or_default`]
let impl__unwrap_or_default
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Default.t_Default v_T)
      (self: t_Option v_T)
    : v_T =
  match self <: t_Option v_T with
  | Option_Some x -> x
  | Option_None  -> Core_models.Default.f_default #v_T #FStar.Tactics.Typeclasses.solve ()

/// See [`std::option::Option::map`]
let impl__map__from__option
      (#v_T #v_U #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_T)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_U})
      (self: t_Option v_T)
      (f: v_F)
    : t_Option v_U =
  match self <: t_Option v_T with
  | Option_Some x ->
    Option_Some
    (Core_models.Ops.Function.f_call_once #v_F #v_T #FStar.Tactics.Typeclasses.solve f (x <: v_T))
    <:
    t_Option v_U
  | Option_None  -> Option_None <: t_Option v_U

/// See [`std::option::Option::map_or`]
let impl__map_or
      (#v_T #v_U #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_T)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_U})
      (self: t_Option v_T)
      (v_default: v_U)
      (f: v_F)
    : v_U =
  match self <: t_Option v_T with
  | Option_Some t ->
    Core_models.Ops.Function.f_call_once #v_F #v_T #FStar.Tactics.Typeclasses.solve f (t <: v_T)
  | Option_None  -> v_default

/// See [`std::option::Option::map_or_else`]
let impl__map_or_else
      (#v_T #v_U #v_D #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Ops.Function.t_FnOnce v_D Prims.unit)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_U})
      (#_: unit{i1.Core_models.Ops.Function.f_Output == v_U})
      (self: t_Option v_T)
      (v_default: v_D)
      (f: v_F)
    : v_U =
  match self <: t_Option v_T with
  | Option_Some t ->
    Core_models.Ops.Function.f_call_once #v_F #v_T #FStar.Tactics.Typeclasses.solve f (t <: v_T)
  | Option_None  ->
    Core_models.Ops.Function.f_call_once #v_D
      #Prims.unit
      #FStar.Tactics.Typeclasses.solve
      v_default
      (() <: Prims.unit)

/// See [`std::option::Option::map_or_default`]
let impl__map_or_default
      (#v_T #v_U #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Default.t_Default v_U)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_U})
      (self: t_Option v_T)
      (f: v_F)
    : v_U =
  match self <: t_Option v_T with
  | Option_Some t ->
    Core_models.Ops.Function.f_call_once #v_F #v_T #FStar.Tactics.Typeclasses.solve f (t <: v_T)
  | Option_None  -> Core_models.Default.f_default #v_U #FStar.Tactics.Typeclasses.solve ()

/// See [`std::option::Option::and_then`]
let impl__and_then
      (#v_T #v_U #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_T)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == t_Option v_U})
      (self: t_Option v_T)
      (f: v_F)
    : t_Option v_U =
  match self <: t_Option v_T with
  | Option_Some x ->
    Core_models.Ops.Function.f_call_once #v_F #v_T #FStar.Tactics.Typeclasses.solve f (x <: v_T)
  | Option_None  -> Option_None <: t_Option v_U

/// See [`std::option::Option::take`]
/// Note: The interface in Rust is wrong, but is good after extraction.
/// We cannot make a useful model with the right interface so we lose the executability.
let impl__take (#v_T: Type0) (self: t_Option v_T) : (t_Option v_T & t_Option v_T) =
  (Option_None <: t_Option v_T), self <: (t_Option v_T & t_Option v_T)

/// See [`std::option::Option::filter`]
assume
val impl__filter':
    #v_T: Type0 ->
    #v_P: Type0 ->
    {| i0: Core_models.Ops.Function.t_FnOnce v_P v_T |} ->
    #_: unit{i0.Core_models.Ops.Function.f_Output == bool} ->
    self: t_Option v_T ->
    predicate: v_P
  -> t_Option v_T

unfold
let impl__filter
      (#v_T #v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_P v_T)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == bool})
     = impl__filter' #v_T #v_P #i0 #_

/// See [`std::option::Option::or`]
let impl__or (#v_T: Type0) (self optb: t_Option v_T) : t_Option v_T =
  match self <: t_Option v_T with
  | Option_Some x -> Option_Some x <: t_Option v_T
  | Option_None  -> optb

/// See [`std::option::Option::or_else`]
let impl__or_else
      (#v_T #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Core_models.Ops.Function.t_FnOnce v_F Prims.unit)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == t_Option v_T})
      (self: t_Option v_T)
      (f: v_F)
    : t_Option v_T =
  match self <: t_Option v_T with
  | Option_Some x -> Option_Some x <: t_Option v_T
  | Option_None  ->
    Core_models.Ops.Function.f_call_once #v_F
      #Prims.unit
      #FStar.Tactics.Typeclasses.solve
      f
      (() <: Prims.unit)

/// See [`std::option::Option::xor`]
let impl__xor (#v_T: Type0) (self optb: t_Option v_T) : t_Option v_T =
  match self, optb <: (t_Option v_T & t_Option v_T) with
  | Option_Some a, Option_None  -> Option_Some a <: t_Option v_T
  | Option_None , Option_Some b -> Option_Some b <: t_Option v_T
  | _ -> Option_None <: t_Option v_T

/// See [`std::option::Option::zip`]
let impl__zip (#v_T #v_U: Type0) (self: t_Option v_T) (other: t_Option v_U) : t_Option (v_T & v_U) =
  match self, other <: (t_Option v_T & t_Option v_U) with
  | Option_Some a, Option_Some b -> Option_Some (a, b <: (v_T & v_U)) <: t_Option (v_T & v_U)
  | _ -> Option_None <: t_Option (v_T & v_U)

/// See [`std::option::Option::inspect`]
let impl__inspect
      (#v_T #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_T)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == Prims.unit})
      (self: t_Option v_T)
      (f: v_F)
    : t_Option v_T =
  let _:Prims.unit =
    match self <: t_Option v_T with
    | Option_Some x ->
      let _:Prims.unit =
        Core_models.Ops.Function.f_call_once #v_F #v_T #FStar.Tactics.Typeclasses.solve f (x <: v_T)
      in
      ()
    | _ -> ()
  in
  self

/// See [`std::option::Option::and`]
let impl__and (#v_T #v_U: Type0) (self: t_Option v_T) (optb: t_Option v_U) : t_Option v_U =
  match self <: t_Option v_T with
  | Option_Some _ -> optb
  | Option_None  -> Option_None <: t_Option v_U

/// See [`std::option::Option::as_slice`]
assume
val impl__as_slice': #v_T: Type0 -> self: t_Option v_T -> t_Slice v_T

unfold
let impl__as_slice (#v_T: Type0) = impl__as_slice' #v_T

/// See [`std::option::Option::insert`]
/// Std takes `&mut self` and returns a `&mut` to the inserted value. The
/// model returns the updated option instead — the same information, since
/// the value std points at is the one this option now holds.
let impl__insert (#v_T: Type0) (self: t_Option v_T) (value: v_T) : t_Option v_T =
  Option_Some value <: t_Option v_T

/// See [`std::option::Option::get_or_insert`]
/// Returns the updated option; see `insert` for why that replaces std\'s
/// `&mut T`.
let impl__get_or_insert (#v_T: Type0) (self: t_Option v_T) (value: v_T) : t_Option v_T =
  match self <: t_Option v_T with
  | Option_Some x -> Option_Some x <: t_Option v_T
  | Option_None  -> Option_Some value <: t_Option v_T

/// See [`std::option::Option::get_or_insert_with`]
/// Returns the updated option; see `insert`.
let impl__get_or_insert_with
      (#v_T #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Core_models.Ops.Function.t_FnOnce v_F Prims.unit)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_T})
      (self: t_Option v_T)
      (f: v_F)
    : t_Option v_T =
  match self <: t_Option v_T with
  | Option_Some x -> Option_Some x <: t_Option v_T
  | Option_None  ->
    Option_Some
    (Core_models.Ops.Function.f_call_once #v_F
        #Prims.unit
        #FStar.Tactics.Typeclasses.solve
        f
        (() <: Prims.unit))
    <:
    t_Option v_T

/// See [`std::option::Option::get_or_insert_default`]
/// Returns the updated option; see `insert`.
let impl__get_or_insert_default
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Default.t_Default v_T)
      (self: t_Option v_T)
    : t_Option v_T =
  match self <: t_Option v_T with
  | Option_Some x -> Option_Some x <: t_Option v_T
  | Option_None  ->
    Option_Some (Core_models.Default.f_default #v_T #FStar.Tactics.Typeclasses.solve ())
    <:
    t_Option v_T

/// See [`std::option::Option::replace`]
/// Like `take`, the Rust interface is wrong here but good after extraction:
/// the model returns `(new self, old value)` instead of mutating in place.
let impl__replace (#v_T: Type0) (self: t_Option v_T) (value: v_T) : (t_Option v_T & t_Option v_T) =
  (Option_Some value <: t_Option v_T), self <: (t_Option v_T & t_Option v_T)

/// See [`std::option::Option::zip_with`]
let impl__zip_with
      (#v_T #v_U #v_F #v_R: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Core_models.Ops.Function.t_FnOnce v_F (v_T & v_U))
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_R})
      (self: t_Option v_T)
      (other: t_Option v_U)
      (f: v_F)
    : t_Option v_R =
  match self, other <: (t_Option v_T & t_Option v_U) with
  | Option_Some a, Option_Some b ->
    Option_Some
    (Core_models.Ops.Function.f_call_once #v_F
        #(v_T & v_U)
        #FStar.Tactics.Typeclasses.solve
        f
        (a, b <: (v_T & v_U)))
    <:
    t_Option v_R
  | _ -> Option_None <: t_Option v_R

/// See [`std::option::Option::is_some`]
let impl__is_some (#v_T: Type0) (self: t_Option v_T)
    : Prims.Pure bool
      Prims.l_True
      (ensures
        fun res ->
          let res:bool = res in
          b2t res ==> Option_Some? self) =
  match self <: t_Option v_T with
  | Option_Some _ -> true
  | _ -> false

/// See [`std::option::Option::is_none`]
let impl__is_none (#v_T: Type0) (self: t_Option v_T) : bool =
  (impl__is_some #v_T self <: bool) =. false

/// See [`std::option::Option::expect`]
let impl__expect (#v_T: Type0) (self: t_Option v_T) (e_msg: string)
    : Prims.Pure v_T (requires impl__is_some #v_T self) (fun _ -> Prims.l_True) =
  match self <: t_Option v_T with
  | Option_Some v_val -> v_val
  | Option_None  -> Core_models.Panicking.Internal.panic #v_T ()

/// See [`std::option::Option::unwrap`]
let impl__unwrap (#v_T: Type0) (self: t_Option v_T)
    : Prims.Pure v_T (requires impl__is_some #v_T self) (fun _ -> Prims.l_True) =
  match self <: t_Option v_T with
  | Option_Some v_val -> v_val
  | Option_None  -> Core_models.Panicking.Internal.panic #v_T ()

/// See [`std::option::Option::unwrap_unchecked`]
/// Calling std\'s version on a `None` is undefined behaviour; the `requires`
/// rules that input out, and the model panics rather than inventing a value.
let impl__unwrap_unchecked (#v_T: Type0) (self: t_Option v_T)
    : Prims.Pure v_T (requires impl__is_some #v_T self) (fun _ -> Prims.l_True) =
  match self <: t_Option v_T with
  | Option_Some x -> x
  | Option_None  -> Core_models.Panicking.Internal.panic #v_T ()

/// See [`std::option::Option::flatten`]
let impl_1__flatten (#v_T: Type0) (self: t_Option (t_Option v_T)) : t_Option v_T =
  match self <: t_Option (t_Option v_T) with
  | Option_Some inner -> inner
  | Option_None  -> Option_None <: t_Option v_T

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2__from__option (#v_T: Type0) : Core_models.Default.t_Default (t_Option v_T) =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: t_Option v_T) -> true);
    f_default = fun (_: Prims.unit) -> Option_None <: t_Option v_T
  }

/// The `None` half of `?` on `Option`: rebuild `None` at the target type. The
/// residual carries `Infallible`, so the `Some` arm is unreachable.
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_6__from__option': #v_T: Type0 -> t_FromResidual (t_Option v_T) (t_Option t_Infallible)

unfold
let impl_6__from__option (#v_T: Type0) = impl_6__from__option' #v_T

/// See [`std::option::Option::unzip`]
let impl_7__unzip (#v_T #v_U: Type0) (self: t_Option (v_T & v_U)) : (t_Option v_T & t_Option v_U) =
  match self <: t_Option (v_T & v_U) with
  | Option_Some (a, b) ->
    (Option_Some a <: t_Option v_T), (Option_Some b <: t_Option v_U)
    <:
    (t_Option v_T & t_Option v_U)
  | Option_None  ->
    (Option_None <: t_Option v_T), (Option_None <: t_Option v_U) <: (t_Option v_T & t_Option v_U)

/// See [`std::option::Option::cloned`]
let impl_8__cloned
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Clone.t_Clone v_T)
      (self: t_Option v_T)
    : t_Option v_T =
  match self <: t_Option v_T with
  | Option_Some x ->
    Option_Some (Core_models.Clone.f_clone #v_T #FStar.Tactics.Typeclasses.solve x) <: t_Option v_T
  | Option_None  -> Option_None <: t_Option v_T

/// See [`std::option::Option::as_deref`]
let impl_9__as_deref (#v_T: Type0) (self: t_Option v_T) : t_Option v_T =
  match self <: t_Option v_T with
  | Option_Some x -> Option_Some x <: t_Option v_T
  | Option_None  -> Option_None <: t_Option v_T

/// See [`std::option::Option::copied`]
let impl_10__copied
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Marker.t_Copy v_T)
      (self: t_Option v_T)
    : t_Option v_T =
  match self <: t_Option v_T with
  | Option_Some x -> Option_Some x <: t_Option v_T
  | Option_None  -> Option_None <: t_Option v_T

/// See [`std::option::Option::flatten_ref`]
let impl_12__flatten_ref (#v_T: Type0) (self: t_Option (t_Option v_T)) : t_Option v_T =
  match self <: t_Option (t_Option v_T) with
  | Option_Some inner -> impl__as_ref__from__option #v_T inner
  | Option_None  -> Option_None <: t_Option v_T

/// See [`std::option::Iter`]
/// An `Option`'s iterators yield at most one element; the payload is a `Seq` so
/// `next` can be written the same way as the slice/array iterators.
type t_Iter (v_T: Type0) = | Iter : Rust_primitives.Sequence.t_Seq v_T -> t_Iter v_T

/// See [`std::option::Option::iter`]
let impl__iter (#v_T: Type0) (self: t_Option v_T) : t_Iter v_T =
  match self <: t_Option v_T with
  | Option_Some x -> Iter (Rust_primitives.Sequence.seq_one #v_T x) <: t_Iter v_T
  | Option_None  -> Iter (Rust_primitives.Sequence.seq_empty #v_T ()) <: t_Iter v_T

/// See [`std::option::IntoIter`]
type t_IntoIter__from__option (v_T: Type0) =
  | IntoIter__from__option : Rust_primitives.Sequence.t_Seq v_T -> t_IntoIter__from__option v_T

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_17__from__option (#v_T: Type0)
    : Core_models.Iter.Traits.Collect.t_IntoIterator (t_Option v_T) =
  {
    f_Item = v_T;
    f_IntoIter = t_IntoIter__from__option v_T;
    f_into_iter_pre = (fun (self: t_Option v_T) -> true);
    f_into_iter_post = (fun (self: t_Option v_T) (out: t_IntoIter__from__option v_T) -> true);
    f_into_iter
    =
    fun (self: t_Option v_T) ->
      match self <: t_Option v_T with
      | Option_Some x ->
        IntoIter__from__option (Rust_primitives.Sequence.seq_one #v_T x)
        <:
        t_IntoIter__from__option v_T
      | Option_None  ->
        IntoIter__from__option (Rust_primitives.Sequence.seq_empty #v_T ())
        <:
        t_IntoIter__from__option v_T
  }

/// See [`std::option::OptionFlatten`]
type t_OptionFlatten (v_A: Type0) = | OptionFlatten : t_Option v_A -> t_OptionFlatten v_A

/// See [`std::option::Option::into_flat_iter`]
/// Std bounds this by `T: IntoIterator<IntoIter = A>` and returns
/// `OptionFlatten<A>`. The model omits the associated-type constraint (as
/// `FromIterator::from_iter` does) and relies on the blanket
/// `IntoIterator for I: Iterator`, under which `A` is `T` itself.
let impl__into_flat_iter (#v_T: Type0) (self: t_Option v_T) : t_OptionFlatten v_T =
  OptionFlatten self <: t_OptionFlatten v_T

/// See [`std::result::Result`]
type t_Result (v_T: Type0) (v_E: Type0) =
  | Result_Ok : v_T -> t_Result v_T v_E
  | Result_Err : v_E -> t_Result v_T v_E

/// See [`std::primitive::u8::from_str_radix`] (and similar for other integer types)
assume
val impl_6__from_str_radix': src: string -> radix: u32
  -> t_Result u8 Core_models.Num.Error.t_ParseIntError

unfold
let impl_6__from_str_radix = impl_6__from_str_radix'

/// See [`std::primitive::u8::from_str_radix`] (and similar for other integer types)
assume
val impl_7__from_str_radix': src: string -> radix: u32
  -> t_Result u16 Core_models.Num.Error.t_ParseIntError

unfold
let impl_7__from_str_radix = impl_7__from_str_radix'

/// See [`std::primitive::u8::from_str_radix`] (and similar for other integer types)
assume
val impl_8__from_str_radix': src: string -> radix: u32
  -> t_Result u32 Core_models.Num.Error.t_ParseIntError

unfold
let impl_8__from_str_radix = impl_8__from_str_radix'

/// See [`std::primitive::u8::from_str_radix`] (and similar for other integer types)
assume
val impl_9__from_str_radix': src: string -> radix: u32
  -> t_Result u64 Core_models.Num.Error.t_ParseIntError

unfold
let impl_9__from_str_radix = impl_9__from_str_radix'

/// See [`std::primitive::u8::from_str_radix`] (and similar for other integer types)
assume
val impl_10__from_str_radix': src: string -> radix: u32
  -> t_Result u128 Core_models.Num.Error.t_ParseIntError

unfold
let impl_10__from_str_radix = impl_10__from_str_radix'

/// See [`std::primitive::u8::from_str_radix`] (and similar for other integer types)
assume
val impl_11__from_str_radix': src: string -> radix: u32
  -> t_Result usize Core_models.Num.Error.t_ParseIntError

unfold
let impl_11__from_str_radix = impl_11__from_str_radix'

/// See [`std::primitive::u8::from_str_radix`] (and similar for other integer types)
assume
val impl_12__from_str_radix': src: string -> radix: u32
  -> t_Result i8 Core_models.Num.Error.t_ParseIntError

unfold
let impl_12__from_str_radix = impl_12__from_str_radix'

/// See [`std::primitive::u8::from_str_radix`] (and similar for other integer types)
assume
val impl_13__from_str_radix': src: string -> radix: u32
  -> t_Result i16 Core_models.Num.Error.t_ParseIntError

unfold
let impl_13__from_str_radix = impl_13__from_str_radix'

/// See [`std::primitive::u8::from_str_radix`] (and similar for other integer types)
assume
val impl_14__from_str_radix': src: string -> radix: u32
  -> t_Result i32 Core_models.Num.Error.t_ParseIntError

unfold
let impl_14__from_str_radix = impl_14__from_str_radix'

/// See [`std::primitive::u8::from_str_radix`] (and similar for other integer types)
assume
val impl_15__from_str_radix': src: string -> radix: u32
  -> t_Result i64 Core_models.Num.Error.t_ParseIntError

unfold
let impl_15__from_str_radix = impl_15__from_str_radix'

/// See [`std::primitive::u8::from_str_radix`] (and similar for other integer types)
assume
val impl_16__from_str_radix': src: string -> radix: u32
  -> t_Result i128 Core_models.Num.Error.t_ParseIntError

unfold
let impl_16__from_str_radix = impl_16__from_str_radix'

/// See [`std::primitive::u8::from_str_radix`] (and similar for other integer types)
assume
val impl_17__from_str_radix': src: string -> radix: u32
  -> t_Result isize Core_models.Num.Error.t_ParseIntError

unfold
let impl_17__from_str_radix = impl_17__from_str_radix'

/// See [`std::ops::ControlFlow::break_ok`]
let impl__break_ok (#v_B #v_C: Type0) (self: t_ControlFlow v_B v_C) : t_Result v_B v_C =
  match self <: t_ControlFlow v_B v_C with
  | ControlFlow_Continue c -> Result_Err c <: t_Result v_B v_C
  | ControlFlow_Break b -> Result_Ok b <: t_Result v_B v_C

/// See [`std::ops::ControlFlow::continue_ok`]
let impl__continue_ok (#v_B #v_C: Type0) (self: t_ControlFlow v_B v_C) : t_Result v_C v_B =
  match self <: t_ControlFlow v_B v_C with
  | ControlFlow_Continue c -> Result_Ok c <: t_Result v_C v_B
  | ControlFlow_Break b -> Result_Err b <: t_Result v_C v_B

/// See [`std::option::Option::ok_or`]
let impl__ok_or (#v_T #v_E: Type0) (self: t_Option v_T) (err: v_E) : t_Result v_T v_E =
  match self <: t_Option v_T with
  | Option_Some v -> Result_Ok v <: t_Result v_T v_E
  | Option_None  -> Result_Err err <: t_Result v_T v_E

/// See [`std::option::Option::ok_or_else`]
let impl__ok_or_else
      (#v_T #v_E #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Core_models.Ops.Function.t_FnOnce v_F Prims.unit)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_E})
      (self: t_Option v_T)
      (err: v_F)
    : t_Result v_T v_E =
  match self <: t_Option v_T with
  | Option_Some v -> Result_Ok v <: t_Result v_T v_E
  | Option_None  ->
    Result_Err
    (Core_models.Ops.Function.f_call_once #v_F
        #Prims.unit
        #FStar.Tactics.Typeclasses.solve
        err
        (() <: Prims.unit))
    <:
    t_Result v_T v_E

/// See [`std::option::Option::get_or_try_insert_with`]
/// Std is generic over any `Try` type through `ops::try_trait::Residual`,
/// which the model does not have; this is the `Result` instance of that
/// signature. Returns the updated option, as `insert` does.
assume
val impl__get_or_try_insert_with':
    #v_T: Type0 ->
    #v_E: Type0 ->
    #v_F: Type0 ->
    {| i0: Core_models.Ops.Function.t_FnOnce v_F Prims.unit |} ->
    #_: unit{i0.Core_models.Ops.Function.f_Output == t_Result v_T v_E} ->
    self: t_Option v_T ->
    f: v_F
  -> t_Result (t_Option v_T) v_E

unfold
let impl__get_or_try_insert_with
      (#v_T #v_E #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Core_models.Ops.Function.t_FnOnce v_F Prims.unit)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == t_Result v_T v_E})
     = impl__get_or_try_insert_with' #v_T #v_E #v_F #i0 #_

/// See [`std::option::Option::transpose`]
let impl_5__transpose (#v_T #v_E: Type0) (self: t_Option (t_Result v_T v_E))
    : t_Result (t_Option v_T) v_E =
  match self <: t_Option (t_Result v_T v_E) with
  | Option_Some (Result_Ok x) ->
    Result_Ok (Option_Some x <: t_Option v_T) <: t_Result (t_Option v_T) v_E
  | Option_Some (Result_Err e) -> Result_Err e <: t_Result (t_Option v_T) v_E
  | Option_None  -> Result_Ok (Option_None <: t_Option v_T) <: t_Result (t_Option v_T) v_E

/// See [`std::result::Result::is_ok`]
let impl__is_ok (#v_T #v_E: Type0) (self: t_Result v_T v_E) : bool =
  match self <: t_Result v_T v_E with
  | Result_Ok _ -> true
  | _ -> false

/// See [`std::result::Result::is_ok_and`]
let impl__is_ok_and
      (#v_T #v_E #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_T)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == bool})
      (self: t_Result v_T v_E)
      (f: v_F)
    : bool =
  match self <: t_Result v_T v_E with
  | Result_Ok t ->
    Core_models.Ops.Function.f_call_once #v_F #v_T #FStar.Tactics.Typeclasses.solve f (t <: v_T)
  | Result_Err _ -> false

/// See [`std::result::Result::is_err`]
let impl__is_err (#v_T #v_E: Type0) (self: t_Result v_T v_E) : bool =
  ~.(impl__is_ok #v_T #v_E self <: bool)

/// See [`std::result::Result::is_err_and`]
let impl__is_err_and
      (#v_T #v_E #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_E)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == bool})
      (self: t_Result v_T v_E)
      (f: v_F)
    : bool =
  match self <: t_Result v_T v_E with
  | Result_Ok _ -> false
  | Result_Err e ->
    Core_models.Ops.Function.f_call_once #v_F #v_E #FStar.Tactics.Typeclasses.solve f (e <: v_E)

/// See [`std::result::Result::as_ref`]
let impl__as_ref__from__result (#v_T #v_E: Type0) (self: t_Result v_T v_E) : t_Result v_T v_E =
  match self <: t_Result v_T v_E with
  | Result_Ok t -> Result_Ok t <: t_Result v_T v_E
  | Result_Err e -> Result_Err e <: t_Result v_T v_E

/// See [`std::result::Result::unwrap_or_else`]
let impl__unwrap_or_else__from__result
      (#v_T #v_E #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_E)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_T})
      (self: t_Result v_T v_E)
      (op: v_F)
    : v_T =
  match self <: t_Result v_T v_E with
  | Result_Ok t -> t
  | Result_Err e ->
    Core_models.Ops.Function.f_call_once #v_F #v_E #FStar.Tactics.Typeclasses.solve op (e <: v_E)

/// See [`std::result::Result::unwrap_or_default`]
let impl__unwrap_or_default__from__result
      (#v_T #v_E: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Default.t_Default v_T)
      (self: t_Result v_T v_E)
    : v_T =
  match self <: t_Result v_T v_E with
  | Result_Ok t -> t
  | Result_Err _ -> Core_models.Default.f_default #v_T #FStar.Tactics.Typeclasses.solve ()

/// See [`std::result::Result::map`]
let impl__map__from__result
      (#v_T #v_E #v_U #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_T)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_U})
      (self: t_Result v_T v_E)
      (op: v_F)
    : t_Result v_U v_E =
  match self <: t_Result v_T v_E with
  | Result_Ok t ->
    Result_Ok
    (Core_models.Ops.Function.f_call_once #v_F #v_T #FStar.Tactics.Typeclasses.solve op (t <: v_T))
    <:
    t_Result v_U v_E
  | Result_Err e -> Result_Err e <: t_Result v_U v_E

/// See [`std::result::Result::map_or`]
let impl__map_or__from__result
      (#v_T #v_E #v_U #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_T)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_U})
      (self: t_Result v_T v_E)
      (v_default: v_U)
      (f: v_F)
    : v_U =
  match self <: t_Result v_T v_E with
  | Result_Ok t ->
    Core_models.Ops.Function.f_call_once #v_F #v_T #FStar.Tactics.Typeclasses.solve f (t <: v_T)
  | Result_Err _ -> v_default

/// See [`std::result::Result::map_or_else`]
let impl__map_or_else__from__result
      (#v_T #v_E #v_U #v_D #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_D v_E)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_FnOnce v_F v_T)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_U})
      (#_: unit{i1.Core_models.Ops.Function.f_Output == v_U})
      (self: t_Result v_T v_E)
      (v_default: v_D)
      (f: v_F)
    : v_U =
  match self <: t_Result v_T v_E with
  | Result_Ok t ->
    Core_models.Ops.Function.f_call_once #v_F #v_T #FStar.Tactics.Typeclasses.solve f (t <: v_T)
  | Result_Err e ->
    Core_models.Ops.Function.f_call_once #v_D
      #v_E
      #FStar.Tactics.Typeclasses.solve
      v_default
      (e <: v_E)

/// See [`std::result::Result::map_or_default`]
let impl__map_or_default__from__result
      (#v_T #v_E #v_U #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Default.t_Default v_U)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_U})
      (self: t_Result v_T v_E)
      (f: v_F)
    : v_U =
  match self <: t_Result v_T v_E with
  | Result_Ok t ->
    Core_models.Ops.Function.f_call_once #v_F #v_T #FStar.Tactics.Typeclasses.solve f (t <: v_T)
  | Result_Err _ -> Core_models.Default.f_default #v_U #FStar.Tactics.Typeclasses.solve ()

/// See [`std::result::Result::inspect`]
let impl__inspect__from__result
      (#v_T #v_E #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_T)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == Prims.unit})
      (self: t_Result v_T v_E)
      (f: v_F)
    : t_Result v_T v_E =
  let _:Prims.unit =
    match self <: t_Result v_T v_E with
    | Result_Ok t ->
      let _:Prims.unit =
        Core_models.Ops.Function.f_call_once #v_F #v_T #FStar.Tactics.Typeclasses.solve f (t <: v_T)
      in
      ()
    | _ -> ()
  in
  self

/// See [`std::result::Result::inspect_err`]
let impl__inspect_err
      (#v_T #v_E #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_E)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == Prims.unit})
      (self: t_Result v_T v_E)
      (f: v_F)
    : t_Result v_T v_E =
  let _:Prims.unit =
    match self <: t_Result v_T v_E with
    | Result_Err e ->
      let _:Prims.unit =
        Core_models.Ops.Function.f_call_once #v_F #v_E #FStar.Tactics.Typeclasses.solve f (e <: v_E)
      in
      ()
    | _ -> ()
  in
  self

/// See [`std::result::Result::ok`]
let impl__ok (#v_T #v_E: Type0) (self: t_Result v_T v_E) : t_Option v_T =
  match self <: t_Result v_T v_E with
  | Result_Ok x -> Option_Some x <: t_Option v_T
  | Result_Err _ -> Option_None <: t_Option v_T

/// See [`std::result::Result::err`]
let impl__err (#v_T #v_E: Type0) (self: t_Result v_T v_E) : t_Option v_E =
  match self <: t_Result v_T v_E with
  | Result_Ok _ -> Option_None <: t_Option v_E
  | Result_Err e -> Option_Some e <: t_Option v_E

/// See [`std::result::Result::and`]
let impl__and__from__result (#v_T #v_E #v_U: Type0) (self: t_Result v_T v_E) (res: t_Result v_U v_E)
    : t_Result v_U v_E =
  match self <: t_Result v_T v_E with
  | Result_Ok _ -> res
  | Result_Err e -> Result_Err e <: t_Result v_U v_E

/// See [`std::result::Result::and_then`]
let impl__and_then__from__result
      (#v_T #v_E #v_U #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_T)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == t_Result v_U v_E})
      (self: t_Result v_T v_E)
      (op: v_F)
    : t_Result v_U v_E =
  match self <: t_Result v_T v_E with
  | Result_Ok t ->
    Core_models.Ops.Function.f_call_once #v_F #v_T #FStar.Tactics.Typeclasses.solve op (t <: v_T)
  | Result_Err e -> Result_Err e <: t_Result v_U v_E

/// See [`std::result::Result::or`]
let impl__or__from__result (#v_T #v_E #v_F: Type0) (self: t_Result v_T v_E) (res: t_Result v_T v_F)
    : t_Result v_T v_F =
  match self <: t_Result v_T v_E with
  | Result_Ok t -> Result_Ok t <: t_Result v_T v_F
  | Result_Err _ -> res

/// See [`std::result::Result::or_else`]
let impl__or_else__from__result
      (#v_T #v_E #v_F #v_O: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_O v_E)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == t_Result v_T v_F})
      (self: t_Result v_T v_E)
      (op: v_O)
    : t_Result v_T v_F =
  match self <: t_Result v_T v_E with
  | Result_Ok t -> Result_Ok t <: t_Result v_T v_F
  | Result_Err e ->
    Core_models.Ops.Function.f_call_once #v_O #v_E #FStar.Tactics.Typeclasses.solve op (e <: v_E)

/// See [`std::result::Result::unwrap_or`]
let impl__unwrap_or__from__result (#v_T #v_E: Type0) (self: t_Result v_T v_E) (v_default: v_T) : v_T =
  match self <: t_Result v_T v_E with
  | Result_Ok t -> t
  | Result_Err _ -> v_default

/// See [`std::result::Result::map_err`]
let impl__map_err
      (#v_T #v_E #v_F #v_O: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_O v_E)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_F})
      (self: t_Result v_T v_E)
      (op: v_O)
    : t_Result v_T v_F =
  match self <: t_Result v_T v_E with
  | Result_Ok t -> Result_Ok t <: t_Result v_T v_F
  | Result_Err e ->
    Result_Err
    (Core_models.Ops.Function.f_call_once #v_O #v_E #FStar.Tactics.Typeclasses.solve op (e <: v_E))
    <:
    t_Result v_T v_F

/// See [`std::result::Result::expect`]
let impl__expect__from__result (#v_T #v_E: Type0) (self: t_Result v_T v_E) (e_msg: string)
    : Prims.Pure v_T (requires impl__is_ok #v_T #v_E self) (fun _ -> Prims.l_True) =
  match self <: t_Result v_T v_E with
  | Result_Ok t -> t
  | Result_Err _ -> Core_models.Panicking.Internal.panic #v_T ()

/// See [`std::result::Result::unwrap`]
let impl__unwrap__from__result (#v_T #v_E: Type0) (self: t_Result v_T v_E)
    : Prims.Pure v_T (requires impl__is_ok #v_T #v_E self) (fun _ -> Prims.l_True) =
  match self <: t_Result v_T v_E with
  | Result_Ok t -> t
  | Result_Err _ -> Core_models.Panicking.Internal.panic #v_T ()

/// See [`std::result::Result::expect_err`]
let impl__expect_err (#v_T #v_E: Type0) (self: t_Result v_T v_E) (e_msg: string)
    : Prims.Pure v_E (requires impl__is_err #v_T #v_E self) (fun _ -> Prims.l_True) =
  match self <: t_Result v_T v_E with
  | Result_Ok _ -> Core_models.Panicking.Internal.panic #v_E ()
  | Result_Err e -> e

/// See [`std::result::Result::unwrap_err`]
let impl__unwrap_err (#v_T #v_E: Type0) (self: t_Result v_T v_E)
    : Prims.Pure v_E (requires impl__is_err #v_T #v_E self) (fun _ -> Prims.l_True) =
  match self <: t_Result v_T v_E with
  | Result_Ok _ -> Core_models.Panicking.Internal.panic #v_E ()
  | Result_Err e -> e

/// See [`std::result::Result::unwrap_unchecked`]
/// Calling std\'s version on an `Err` is undefined behaviour; the `requires`
/// rules that input out, and the model panics rather than inventing a value.
let impl__unwrap_unchecked__from__result (#v_T #v_E: Type0) (self: t_Result v_T v_E)
    : Prims.Pure v_T (requires impl__is_ok #v_T #v_E self) (fun _ -> Prims.l_True) =
  match self <: t_Result v_T v_E with
  | Result_Ok t -> t
  | Result_Err _ -> Core_models.Panicking.Internal.panic #v_T ()

/// See [`std::result::Result::unwrap_err_unchecked`]
/// See `unwrap_unchecked` for why the `Ok` arm panics.
let impl__unwrap_err_unchecked (#v_T #v_E: Type0) (self: t_Result v_T v_E)
    : Prims.Pure v_E (requires impl__is_err #v_T #v_E self) (fun _ -> Prims.l_True) =
  match self <: t_Result v_T v_E with
  | Result_Ok _ -> Core_models.Panicking.Internal.panic #v_E ()
  | Result_Err e -> e

/// See [`std::result::Result::cloned`]
let impl_1__cloned__from__result
      (#v_T #v_E: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Clone.t_Clone v_T)
      (self: t_Result v_T v_E)
    : t_Result v_T v_E =
  match self <: t_Result v_T v_E with
  | Result_Ok t ->
    Result_Ok (Core_models.Clone.f_clone #v_T #FStar.Tactics.Typeclasses.solve t)
    <:
    t_Result v_T v_E
  | Result_Err e -> Result_Err e <: t_Result v_T v_E

/// See [`std::result::Result::transpose`]
let impl_2__transpose (#v_T #v_E: Type0) (self: t_Result (t_Option v_T) v_E)
    : t_Option (t_Result v_T v_E) =
  match self <: t_Result (t_Option v_T) v_E with
  | Result_Ok (Option_Some t) ->
    Option_Some (Result_Ok t <: t_Result v_T v_E) <: t_Option (t_Result v_T v_E)
  | Result_Ok (Option_None ) -> Option_None <: t_Option (t_Result v_T v_E)
  | Result_Err e -> Option_Some (Result_Err e <: t_Result v_T v_E) <: t_Option (t_Result v_T v_E)

/// See [`std::result::Result::flatten`]
let impl_3__flatten (#v_T #v_E: Type0) (self: t_Result (t_Result v_T v_E) v_E) : t_Result v_T v_E =
  match self <: t_Result (t_Result v_T v_E) v_E with
  | Result_Ok inner -> inner
  | Result_Err e -> Result_Err e <: t_Result v_T v_E

/// Models the std impl `FromIterator<Result<A, E>> for Result<V, E>`: collect
/// an iterator of `Result`s into a `Result` of a collection, short-circuiting
/// on the first `Err`.
/// Opaque: our `FromIterator::from_iter` signature deliberately omits the
/// `Item = ...` bound (to avoid the associated-type constraint), so the
/// short-circuiting body cannot be written in terms of the iterator\'s items;
/// the behaviour is axiomatised. The body below exists only to typecheck —
/// it delegates to `V`\'s own `from_iter`.
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_4__from__result':
    #v_A: Type0 ->
    #v_E: Type0 ->
    #v_V: Type0 ->
    {| i0: Core_models.Iter.Traits.Collect.t_FromIterator v_V v_A |}
  -> Core_models.Iter.Traits.Collect.t_FromIterator (t_Result v_V v_E) (t_Result v_A v_E)

unfold
let impl_4__from__result
      (#v_A #v_E #v_V: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Core_models.Iter.Traits.Collect.t_FromIterator v_V v_A)
     = impl_4__from__result' #v_A #v_E #v_V #i0

/// See [`std::result::Iter`]
/// A `Result`'s iterators yield at most one element; the payload is a `Seq` so
/// `next` can be written the same way as the slice/array iterators.
type t_Iter__from__result (v_T: Type0) =
  | Iter__from__result : Rust_primitives.Sequence.t_Seq v_T -> t_Iter__from__result v_T

/// See [`std::result::Result::iter`]
let impl__iter__from__result (#v_T #v_E: Type0) (self: t_Result v_T v_E) : t_Iter__from__result v_T =
  match self <: t_Result v_T v_E with
  | Result_Ok t ->
    Iter__from__result (Rust_primitives.Sequence.seq_one #v_T t) <: t_Iter__from__result v_T
  | Result_Err _ ->
    Iter__from__result (Rust_primitives.Sequence.seq_empty #v_T ()) <: t_Iter__from__result v_T

/// See [`std::result::IntoIter`]
type t_IntoIter__from__result (v_T: Type0) =
  | IntoIter__from__result : Rust_primitives.Sequence.t_Seq v_T -> t_IntoIter__from__result v_T

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10__from__result (#v_T #v_E: Type0)
    : Core_models.Iter.Traits.Collect.t_IntoIterator (t_Result v_T v_E) =
  {
    f_Item = v_T;
    f_IntoIter = t_IntoIter__from__result v_T;
    f_into_iter_pre = (fun (self: t_Result v_T v_E) -> true);
    f_into_iter_post = (fun (self: t_Result v_T v_E) (out: t_IntoIter__from__result v_T) -> true);
    f_into_iter
    =
    fun (self: t_Result v_T v_E) ->
      match self <: t_Result v_T v_E with
      | Result_Ok t ->
        IntoIter__from__result (Rust_primitives.Sequence.seq_one #v_T t)
        <:
        t_IntoIter__from__result v_T
      | Result_Err _ ->
        IntoIter__from__result (Rust_primitives.Sequence.seq_empty #v_T ())
        <:
        t_IntoIter__from__result v_T
  }

/// See [`std::result::Result::as_deref`]
let impl_11__as_deref (#v_T #v_E: Type0) (self: t_Result v_T v_E) : t_Result v_T v_E =
  match self <: t_Result v_T v_E with
  | Result_Ok t -> Result_Ok t <: t_Result v_T v_E
  | Result_Err e -> Result_Err e <: t_Result v_T v_E

/// See [`std::result::Result::copied`]
let impl_13__copied
      (#v_T #v_E: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Marker.t_Copy v_T)
      (self: t_Result v_T v_E)
    : t_Result v_T v_E =
  match self <: t_Result v_T v_E with
  | Result_Ok t -> Result_Ok t <: t_Result v_T v_E
  | Result_Err e -> Result_Err e <: t_Result v_T v_E

/// See [`std::result::Result::into_ok`]
let impl_14__into_ok (#v_T: Type0) (self: t_Result v_T t_Infallible)
    : Prims.Pure v_T (requires impl__is_ok #v_T #t_Infallible self) (fun _ -> Prims.l_True) =
  match self <: t_Result v_T t_Infallible with
  | Result_Ok t -> t
  | Result_Err _ -> Core_models.Panicking.Internal.panic #v_T ()

/// See [`std::result::Result::into_err`]
let impl_15__into_err (#v_E: Type0) (self: t_Result t_Infallible v_E)
    : Prims.Pure v_E (requires impl__is_err #t_Infallible #v_E self) (fun _ -> Prims.l_True) =
  match self <: t_Result t_Infallible v_E with
  | Result_Ok _ -> Core_models.Panicking.Internal.panic #v_E ()
  | Result_Err e -> e

/// See [`std::cmp::PartialEq`]
class t_PartialEq (v_Self: Type0) (v_Rhs: Type0) = {
  f_eq_pre:self_: v_Self -> other: v_Rhs -> pred: Type0{true ==> pred};
  f_eq_post:v_Self -> v_Rhs -> bool -> Type0;
  f_eq:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure bool (f_eq_pre x0 x1) (fun result -> f_eq_post x0 x1 result)
}

class t_Neq (v_Self: Type0) (v_Rhs: Type0) = {
  f_neq_pre:self_: v_Self -> y: v_Rhs -> pred: Type0{true ==> pred};
  f_neq_post:v_Self -> v_Rhs -> bool -> Type0;
  f_neq:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure bool (f_neq_pre x0 x1) (fun result -> f_neq_post x0 x1 result)
}

/// See [`std::convert::Into`]
class t_Into (v_Self: Type0) (v_T: Type0) = {
  f_into_pre:self_: v_Self -> pred: Type0{true ==> pred};
  f_into_post:v_Self -> v_T -> Type0;
  f_into:x0: v_Self -> Prims.Pure v_T (f_into_pre x0) (fun result -> f_into_post x0 result)
}

/// See [`std::convert::From`]
class t_From (v_Self: Type0) (v_T: Type0) = {
  f_from_pre:x: v_T -> pred: Type0{true ==> pred};
  f_from_post:v_T -> v_Self -> Type0;
  f_from:x0: v_T -> Prims.Pure v_Self (f_from_pre x0) (fun result -> f_from_post x0 result)
}

/// See [`std::convert::AsRef`]
class t_AsRef (v_Self: Type0) (v_T: Type0) = {
  f_as_ref_pre:self_: v_Self -> pred: Type0{true ==> pred};
  f_as_ref_post:v_Self -> v_T -> Type0;
  f_as_ref:x0: v_Self -> Prims.Pure v_T (f_as_ref_pre x0) (fun result -> f_as_ref_post x0 result)
}

/// See [`std::ops::Try`]
class t_Try (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Output:Type0;
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Residual:Type0;
  f_from_output_pre:f_Output -> Type0;
  f_from_output_post:f_Output -> v_Self -> Type0;
  f_from_output:x0: f_Output
    -> Prims.Pure v_Self (f_from_output_pre x0) (fun result -> f_from_output_post x0 result);
  f_branch_pre:v_Self -> Type0;
  f_branch_post:v_Self -> t_ControlFlow f_Residual f_Output -> Type0;
  f_branch:x0: v_Self
    -> Prims.Pure (t_ControlFlow f_Residual f_Output)
        (f_branch_pre x0)
        (fun result -> f_branch_post x0 result)
}

/// See [`std::cmp::Eq`]
class t_Eq (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:t_PartialEq v_Self v_Self
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_Eq v_Self|} -> i._super_i0

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl__from__cmp
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_PartialEq v_T v_T)
    : t_Neq v_T v_T =
  {
    f_neq_pre = (fun (self: v_T) (y: v_T) -> true);
    f_neq_post = (fun (self: v_T) (y: v_T) (out: bool) -> true);
    f_neq
    =
    fun (self: v_T) (y: v_T) ->
      (f_eq #v_T #v_T #FStar.Tactics.Typeclasses.solve self y <: bool) =. false
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3 (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_PartialEq v_T v_T)
    : t_PartialEq (t_Reverse v_T) (t_Reverse v_T) =
  {
    f_eq_pre = (fun (self: t_Reverse v_T) (other: t_Reverse v_T) -> true);
    f_eq_post = (fun (self: t_Reverse v_T) (other: t_Reverse v_T) (out: bool) -> true);
    f_eq
    =
    fun (self: t_Reverse v_T) (other: t_Reverse v_T) ->
      f_eq #v_T #v_T #FStar.Tactics.Typeclasses.solve other._0 self._0
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4 (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Eq v_T)
    : t_Eq (t_Reverse v_T) = { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6: t_PartialEq u8 u8 =
  {
    f_eq_pre = (fun (self: u8) (other: u8) -> true);
    f_eq_post = (fun (self: u8) (other: u8) (out: bool) -> true);
    f_eq = fun (self: u8) (other: u8) -> self =. other
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7: t_Eq u8 = { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8: t_PartialEq i8 i8 =
  {
    f_eq_pre = (fun (self: i8) (other: i8) -> true);
    f_eq_post = (fun (self: i8) (other: i8) (out: bool) -> true);
    f_eq = fun (self: i8) (other: i8) -> self =. other
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9: t_Eq i8 = { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10: t_PartialEq u16 u16 =
  {
    f_eq_pre = (fun (self: u16) (other: u16) -> true);
    f_eq_post = (fun (self: u16) (other: u16) (out: bool) -> true);
    f_eq = fun (self: u16) (other: u16) -> self =. other
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_11: t_Eq u16 = { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_12: t_PartialEq i16 i16 =
  {
    f_eq_pre = (fun (self: i16) (other: i16) -> true);
    f_eq_post = (fun (self: i16) (other: i16) (out: bool) -> true);
    f_eq = fun (self: i16) (other: i16) -> self =. other
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_13: t_Eq i16 = { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_14: t_PartialEq u32 u32 =
  {
    f_eq_pre = (fun (self: u32) (other: u32) -> true);
    f_eq_post = (fun (self: u32) (other: u32) (out: bool) -> true);
    f_eq = fun (self: u32) (other: u32) -> self =. other
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_15: t_Eq u32 = { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_16: t_PartialEq i32 i32 =
  {
    f_eq_pre = (fun (self: i32) (other: i32) -> true);
    f_eq_post = (fun (self: i32) (other: i32) (out: bool) -> true);
    f_eq = fun (self: i32) (other: i32) -> self =. other
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_17: t_Eq i32 = { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_18: t_PartialEq u64 u64 =
  {
    f_eq_pre = (fun (self: u64) (other: u64) -> true);
    f_eq_post = (fun (self: u64) (other: u64) (out: bool) -> true);
    f_eq = fun (self: u64) (other: u64) -> self =. other
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_19: t_Eq u64 = { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_20: t_PartialEq i64 i64 =
  {
    f_eq_pre = (fun (self: i64) (other: i64) -> true);
    f_eq_post = (fun (self: i64) (other: i64) (out: bool) -> true);
    f_eq = fun (self: i64) (other: i64) -> self =. other
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_21: t_Eq i64 = { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_22: t_PartialEq u128 u128 =
  {
    f_eq_pre = (fun (self: u128) (other: u128) -> true);
    f_eq_post = (fun (self: u128) (other: u128) (out: bool) -> true);
    f_eq = fun (self: u128) (other: u128) -> self =. other
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_23: t_Eq u128 = { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_24__from__cmp: t_PartialEq i128 i128 =
  {
    f_eq_pre = (fun (self: i128) (other: i128) -> true);
    f_eq_post = (fun (self: i128) (other: i128) (out: bool) -> true);
    f_eq = fun (self: i128) (other: i128) -> self =. other
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_25__from__cmp: t_Eq i128 = { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_26__from__cmp: t_PartialEq usize usize =
  {
    f_eq_pre = (fun (self: usize) (other: usize) -> true);
    f_eq_post = (fun (self: usize) (other: usize) (out: bool) -> true);
    f_eq = fun (self: usize) (other: usize) -> self =. other
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_27__from__cmp: t_Eq usize = { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_28__from__cmp: t_PartialEq isize isize =
  {
    f_eq_pre = (fun (self: isize) (other: isize) -> true);
    f_eq_post = (fun (self: isize) (other: isize) (out: bool) -> true);
    f_eq = fun (self: isize) (other: isize) -> self =. other
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_29__from__cmp: t_Eq isize = { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl__from__convert
      (#v_T #v_U: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_From v_U v_T)
    : t_Into v_T v_U =
  {
    f_into_pre = (fun (self: v_T) -> true);
    f_into_post = (fun (self: v_T) (out: v_U) -> true);
    f_into = fun (self: v_T) -> f_from #v_U #v_T #FStar.Tactics.Typeclasses.solve self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4__from__convert (#v_T: Type0) : t_From v_T v_T =
  {
    f_from_pre = (fun (x: v_T) -> true);
    f_from_post = (fun (x: v_T) (out: v_T) -> true);
    f_from = fun (x: v_T) -> x
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5__from__convert (#v_T: Type0) : t_AsRef (t_Slice v_T) (t_Slice v_T) =
  {
    f_as_ref_pre = (fun (self: t_Slice v_T) -> true);
    f_as_ref_post = (fun (self: t_Slice v_T) (out: t_Slice v_T) -> true);
    f_as_ref = fun (self: t_Slice v_T) -> self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6__from__convert: t_From u16 u8 =
  {
    f_from_pre = (fun (x: u8) -> true);
    f_from_post = (fun (x: u8) (out: u16) -> true);
    f_from = fun (x: u8) -> cast (x <: u8) <: u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7__from__convert: t_From u32 u8 =
  {
    f_from_pre = (fun (x: u8) -> true);
    f_from_post = (fun (x: u8) (out: u32) -> true);
    f_from = fun (x: u8) -> cast (x <: u8) <: u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8__from__convert: t_From u32 u16 =
  {
    f_from_pre = (fun (x: u16) -> true);
    f_from_post = (fun (x: u16) (out: u32) -> true);
    f_from = fun (x: u16) -> cast (x <: u16) <: u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9__from__convert: t_From u64 u8 =
  {
    f_from_pre = (fun (x: u8) -> true);
    f_from_post = (fun (x: u8) (out: u64) -> true);
    f_from = fun (x: u8) -> cast (x <: u8) <: u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10__from__convert: t_From u64 u16 =
  {
    f_from_pre = (fun (x: u16) -> true);
    f_from_post = (fun (x: u16) (out: u64) -> true);
    f_from = fun (x: u16) -> cast (x <: u16) <: u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_11__from__convert: t_From u64 u32 =
  {
    f_from_pre = (fun (x: u32) -> true);
    f_from_post = (fun (x: u32) (out: u64) -> true);
    f_from = fun (x: u32) -> cast (x <: u32) <: u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_12__from__convert: t_From u128 u8 =
  {
    f_from_pre = (fun (x: u8) -> true);
    f_from_post = (fun (x: u8) (out: u128) -> true);
    f_from = fun (x: u8) -> cast (x <: u8) <: u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_13__from__convert: t_From u128 u16 =
  {
    f_from_pre = (fun (x: u16) -> true);
    f_from_post = (fun (x: u16) (out: u128) -> true);
    f_from = fun (x: u16) -> cast (x <: u16) <: u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_14__from__convert: t_From u128 u32 =
  {
    f_from_pre = (fun (x: u32) -> true);
    f_from_post = (fun (x: u32) (out: u128) -> true);
    f_from = fun (x: u32) -> cast (x <: u32) <: u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_15__from__convert: t_From u128 u64 =
  {
    f_from_pre = (fun (x: u64) -> true);
    f_from_post = (fun (x: u64) (out: u128) -> true);
    f_from = fun (x: u64) -> cast (x <: u64) <: u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_16__from__convert: t_From usize u8 =
  {
    f_from_pre = (fun (x: u8) -> true);
    f_from_post = (fun (x: u8) (out: usize) -> true);
    f_from = fun (x: u8) -> cast (x <: u8) <: usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_17__from__convert: t_From usize u16 =
  {
    f_from_pre = (fun (x: u16) -> true);
    f_from_post = (fun (x: u16) (out: usize) -> true);
    f_from = fun (x: u16) -> cast (x <: u16) <: usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_18__from__convert: t_From i16 i8 =
  {
    f_from_pre = (fun (x: i8) -> true);
    f_from_post = (fun (x: i8) (out: i16) -> true);
    f_from = fun (x: i8) -> cast (x <: i8) <: i16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_19__from__convert: t_From i32 i8 =
  {
    f_from_pre = (fun (x: i8) -> true);
    f_from_post = (fun (x: i8) (out: i32) -> true);
    f_from = fun (x: i8) -> cast (x <: i8) <: i32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_20__from__convert: t_From i32 i16 =
  {
    f_from_pre = (fun (x: i16) -> true);
    f_from_post = (fun (x: i16) (out: i32) -> true);
    f_from = fun (x: i16) -> cast (x <: i16) <: i32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_21__from__convert: t_From i64 i8 =
  {
    f_from_pre = (fun (x: i8) -> true);
    f_from_post = (fun (x: i8) (out: i64) -> true);
    f_from = fun (x: i8) -> cast (x <: i8) <: i64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_22__from__convert: t_From i64 i16 =
  {
    f_from_pre = (fun (x: i16) -> true);
    f_from_post = (fun (x: i16) (out: i64) -> true);
    f_from = fun (x: i16) -> cast (x <: i16) <: i64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_23__from__convert: t_From i64 i32 =
  {
    f_from_pre = (fun (x: i32) -> true);
    f_from_post = (fun (x: i32) (out: i64) -> true);
    f_from = fun (x: i32) -> cast (x <: i32) <: i64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_24__from__convert: t_From i128 i8 =
  {
    f_from_pre = (fun (x: i8) -> true);
    f_from_post = (fun (x: i8) (out: i128) -> true);
    f_from = fun (x: i8) -> cast (x <: i8) <: i128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_25__from__convert: t_From i128 i16 =
  {
    f_from_pre = (fun (x: i16) -> true);
    f_from_post = (fun (x: i16) (out: i128) -> true);
    f_from = fun (x: i16) -> cast (x <: i16) <: i128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_26__from__convert: t_From i128 i32 =
  {
    f_from_pre = (fun (x: i32) -> true);
    f_from_post = (fun (x: i32) (out: i128) -> true);
    f_from = fun (x: i32) -> cast (x <: i32) <: i128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_27__from__convert: t_From i128 i64 =
  {
    f_from_pre = (fun (x: i64) -> true);
    f_from_post = (fun (x: i64) (out: i128) -> true);
    f_from = fun (x: i64) -> cast (x <: i64) <: i128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_28__from__convert: t_From isize i8 =
  {
    f_from_pre = (fun (x: i8) -> true);
    f_from_post = (fun (x: i8) (out: isize) -> true);
    f_from = fun (x: i8) -> cast (x <: i8) <: isize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_29__from__convert: t_From isize i16 =
  {
    f_from_pre = (fun (x: i16) -> true);
    f_from_post = (fun (x: i16) (out: isize) -> true);
    f_from = fun (x: i16) -> cast (x <: i16) <: isize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_30__from__convert: t_From i16 u8 =
  {
    f_from_pre = (fun (x: u8) -> true);
    f_from_post = (fun (x: u8) (out: i16) -> true);
    f_from = fun (x: u8) -> cast (x <: u8) <: i16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_31: t_From i32 u8 =
  {
    f_from_pre = (fun (x: u8) -> true);
    f_from_post = (fun (x: u8) (out: i32) -> true);
    f_from = fun (x: u8) -> cast (x <: u8) <: i32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_32__from__convert: t_From i64 u8 =
  {
    f_from_pre = (fun (x: u8) -> true);
    f_from_post = (fun (x: u8) (out: i64) -> true);
    f_from = fun (x: u8) -> cast (x <: u8) <: i64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_33: t_From i128 u8 =
  {
    f_from_pre = (fun (x: u8) -> true);
    f_from_post = (fun (x: u8) (out: i128) -> true);
    f_from = fun (x: u8) -> cast (x <: u8) <: i128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_34__from__convert: t_From isize u8 =
  {
    f_from_pre = (fun (x: u8) -> true);
    f_from_post = (fun (x: u8) (out: isize) -> true);
    f_from = fun (x: u8) -> cast (x <: u8) <: isize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_35: t_From i32 u16 =
  {
    f_from_pre = (fun (x: u16) -> true);
    f_from_post = (fun (x: u16) (out: i32) -> true);
    f_from = fun (x: u16) -> cast (x <: u16) <: i32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_36__from__convert: t_From i64 u16 =
  {
    f_from_pre = (fun (x: u16) -> true);
    f_from_post = (fun (x: u16) (out: i64) -> true);
    f_from = fun (x: u16) -> cast (x <: u16) <: i64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_37: t_From i128 u16 =
  {
    f_from_pre = (fun (x: u16) -> true);
    f_from_post = (fun (x: u16) (out: i128) -> true);
    f_from = fun (x: u16) -> cast (x <: u16) <: i128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_38__from__convert: t_From i64 u32 =
  {
    f_from_pre = (fun (x: u32) -> true);
    f_from_post = (fun (x: u32) (out: i64) -> true);
    f_from = fun (x: u32) -> cast (x <: u32) <: i64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_39: t_From i128 u32 =
  {
    f_from_pre = (fun (x: u32) -> true);
    f_from_post = (fun (x: u32) (out: i128) -> true);
    f_from = fun (x: u32) -> cast (x <: u32) <: i128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_40__from__convert: t_From i128 u64 =
  {
    f_from_pre = (fun (x: u64) -> true);
    f_from_post = (fun (x: u64) (out: i128) -> true);
    f_from = fun (x: u64) -> cast (x <: u64) <: i128
  }

/// See [`std::ops::RangeBounds`]
class t_RangeBounds (v_Self: Type0) (v_T: Type0) = {
  f_start_bound_pre:self_: v_Self -> pred: Type0{true ==> pred};
  f_start_bound_post:v_Self -> t_Bound v_T -> Type0;
  f_start_bound:x0: v_Self
    -> Prims.Pure (t_Bound v_T) (f_start_bound_pre x0) (fun result -> f_start_bound_post x0 result);
  f_end_bound_pre:self_: v_Self -> pred: Type0{true ==> pred};
  f_end_bound_post:v_Self -> t_Bound v_T -> Type0;
  f_end_bound:x0: v_Self
    -> Prims.Pure (t_Bound v_T) (f_end_bound_pre x0) (fun result -> f_end_bound_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5 (#v_T: Type0) : t_RangeBounds (t_Range v_T) v_T =
  {
    f_start_bound_pre = (fun (self: t_Range v_T) -> true);
    f_start_bound_post = (fun (self: t_Range v_T) (out: t_Bound v_T) -> true);
    f_start_bound = (fun (self: t_Range v_T) -> Bound_Included self.f_start <: t_Bound v_T);
    f_end_bound_pre = (fun (self: t_Range v_T) -> true);
    f_end_bound_post = (fun (self: t_Range v_T) (out: t_Bound v_T) -> true);
    f_end_bound = fun (self: t_Range v_T) -> Bound_Excluded self.f_end <: t_Bound v_T
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6__from__range (#v_T: Type0) : t_RangeBounds (t_RangeFrom v_T) v_T =
  {
    f_start_bound_pre = (fun (self: t_RangeFrom v_T) -> true);
    f_start_bound_post = (fun (self: t_RangeFrom v_T) (out: t_Bound v_T) -> true);
    f_start_bound = (fun (self: t_RangeFrom v_T) -> Bound_Included self.f_start <: t_Bound v_T);
    f_end_bound_pre = (fun (self: t_RangeFrom v_T) -> true);
    f_end_bound_post = (fun (self: t_RangeFrom v_T) (out: t_Bound v_T) -> true);
    f_end_bound = fun (self: t_RangeFrom v_T) -> Bound_Unbounded <: t_Bound v_T
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7__from__range (#v_T: Type0) : t_RangeBounds (t_RangeTo v_T) v_T =
  {
    f_start_bound_pre = (fun (self: t_RangeTo v_T) -> true);
    f_start_bound_post = (fun (self: t_RangeTo v_T) (out: t_Bound v_T) -> true);
    f_start_bound = (fun (self: t_RangeTo v_T) -> Bound_Unbounded <: t_Bound v_T);
    f_end_bound_pre = (fun (self: t_RangeTo v_T) -> true);
    f_end_bound_post = (fun (self: t_RangeTo v_T) (out: t_Bound v_T) -> true);
    f_end_bound = fun (self: t_RangeTo v_T) -> Bound_Excluded self.f_end <: t_Bound v_T
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8__from__range (#v_T: Type0) : t_RangeBounds t_RangeFull v_T =
  {
    f_start_bound_pre = (fun (self: t_RangeFull) -> true);
    f_start_bound_post = (fun (self: t_RangeFull) (out: t_Bound v_T) -> true);
    f_start_bound = (fun (self: t_RangeFull) -> Bound_Unbounded <: t_Bound v_T);
    f_end_bound_pre = (fun (self: t_RangeFull) -> true);
    f_end_bound_post = (fun (self: t_RangeFull) (out: t_Bound v_T) -> true);
    f_end_bound = fun (self: t_RangeFull) -> Bound_Unbounded <: t_Bound v_T
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9__from__range (#v_T: Type0) : t_RangeBounds (t_RangeInclusive v_T) v_T =
  {
    f_start_bound_pre = (fun (self: t_RangeInclusive v_T) -> true);
    f_start_bound_post = (fun (self: t_RangeInclusive v_T) (out: t_Bound v_T) -> true);
    f_start_bound = (fun (self: t_RangeInclusive v_T) -> Bound_Included self.f_start <: t_Bound v_T);
    f_end_bound_pre = (fun (self: t_RangeInclusive v_T) -> true);
    f_end_bound_post = (fun (self: t_RangeInclusive v_T) (out: t_Bound v_T) -> true);
    f_end_bound = fun (self: t_RangeInclusive v_T) -> Bound_Included self.f_end <: t_Bound v_T
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10__from__range (#v_T: Type0) : t_RangeBounds (t_RangeToInclusive v_T) v_T =
  {
    f_start_bound_pre = (fun (self: t_RangeToInclusive v_T) -> true);
    f_start_bound_post = (fun (self: t_RangeToInclusive v_T) (out: t_Bound v_T) -> true);
    f_start_bound = (fun (self: t_RangeToInclusive v_T) -> Bound_Unbounded <: t_Bound v_T);
    f_end_bound_pre = (fun (self: t_RangeToInclusive v_T) -> true);
    f_end_bound_post = (fun (self: t_RangeToInclusive v_T) (out: t_Bound v_T) -> true);
    f_end_bound = fun (self: t_RangeToInclusive v_T) -> Bound_Included self.f_end <: t_Bound v_T
  }

/// See [`std::option::Option::reduce`]
/// Std bounds the two payloads by `Into<R>`; the model\'s `convert::Into` is
/// private (it is derived from `From` by a blanket impl), so the bound is
/// spelled on `From` here.
let impl__reduce
      (#v_T #v_U #v_R #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_From v_R v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_From v_R v_U)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Core_models.Ops.Function.t_FnOnce v_F (v_T & v_U))
      (#_: unit{i2.Core_models.Ops.Function.f_Output == v_R})
      (self: t_Option v_T)
      (other: t_Option v_U)
      (f: v_F)
    : t_Option v_R =
  match self, other <: (t_Option v_T & t_Option v_U) with
  | Option_Some a, Option_Some b ->
    Option_Some
    (Core_models.Ops.Function.f_call_once #v_F
        #(v_T & v_U)
        #FStar.Tactics.Typeclasses.solve
        f
        (a, b <: (v_T & v_U)))
    <:
    t_Option v_R
  | Option_Some a, Option_None  ->
    Option_Some (f_from #v_R #v_T #FStar.Tactics.Typeclasses.solve a) <: t_Option v_R
  | Option_None , Option_Some b ->
    Option_Some (f_from #v_R #v_U #FStar.Tactics.Typeclasses.solve b) <: t_Option v_R
  | Option_None , Option_None  -> Option_None <: t_Option v_R

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3__from__option
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_PartialEq v_T v_T)
    : t_PartialEq (t_Option v_T) (t_Option v_T) =
  {
    f_eq_pre = (fun (self: t_Option v_T) (other: t_Option v_T) -> true);
    f_eq_post = (fun (self: t_Option v_T) (other: t_Option v_T) (out: bool) -> true);
    f_eq
    =
    fun (self: t_Option v_T) (other: t_Option v_T) ->
      match self, other <: (t_Option v_T & t_Option v_T) with
      | Option_Some a, Option_Some b -> f_eq #v_T #v_T #FStar.Tactics.Typeclasses.solve a b
      | Option_None , Option_None  -> true
      | _ -> false
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4__from__option (#v_T: Type0) : t_Try (t_Option v_T) =
  {
    f_Output = v_T;
    f_Residual = t_Option t_Infallible;
    f_from_output_pre = (fun (output: v_T) -> true);
    f_from_output_post = (fun (output: v_T) (out: t_Option v_T) -> true);
    f_from_output = (fun (output: v_T) -> Option_Some output <: t_Option v_T);
    f_branch_pre = (fun (self: t_Option v_T) -> true);
    f_branch_post
    =
    (fun (self: t_Option v_T) (out: t_ControlFlow (t_Option t_Infallible) v_T) -> true);
    f_branch
    =
    fun (self: t_Option v_T) ->
      match self <: t_Option v_T with
      | Option_Some v -> ControlFlow_Continue v <: t_ControlFlow (t_Option t_Infallible) v_T
      | Option_None  ->
        ControlFlow_Break (Option_None <: t_Option t_Infallible)
        <:
        t_ControlFlow (t_Option t_Infallible) v_T
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5__from__result (#v_T #v_E: Type0) : t_Try (t_Result v_T v_E) =
  {
    f_Output = v_T;
    f_Residual = t_Result t_Infallible v_E;
    f_from_output_pre = (fun (output: v_T) -> true);
    f_from_output_post = (fun (output: v_T) (out: t_Result v_T v_E) -> true);
    f_from_output = (fun (output: v_T) -> Result_Ok output <: t_Result v_T v_E);
    f_branch_pre = (fun (self: t_Result v_T v_E) -> true);
    f_branch_post
    =
    (fun (self: t_Result v_T v_E) (out: t_ControlFlow (t_Result t_Infallible v_E) v_T) -> true);
    f_branch
    =
    fun (self: t_Result v_T v_E) ->
      match self <: t_Result v_T v_E with
      | Result_Ok v -> ControlFlow_Continue v <: t_ControlFlow (t_Result t_Infallible v_E) v_T
      | Result_Err e ->
        ControlFlow_Break (Result_Err e <: t_Result t_Infallible v_E)
        <:
        t_ControlFlow (t_Result t_Infallible v_E) v_T
  }

/// The error half of `?`: re-inject the `Err(e)` residual, widening the error
/// via `From` (mirrors std\'s `impl<T, E, F: From<E>> ... for Result<T, F>`). `Ok`
/// is unreachable — the residual\'s payload is `Infallible`.
[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_6__from__result': #v_T: Type0 -> #v_E: Type0 -> #v_F: Type0 -> {| i0: t_From v_F v_E |}
  -> t_FromResidual (t_Result v_T v_F) (t_Result t_Infallible v_E)

unfold
let impl_6__from__result
      (#v_T #v_E #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_From v_F v_E)
     = impl_6__from__result' #v_T #v_E #v_F #i0

/// See [`std::cmp::PartialOrd`]
class t_PartialOrd (v_Self: Type0) (v_Rhs: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:t_PartialEq v_Self v_Rhs;
  f_partial_cmp_pre:self_: v_Self -> other: v_Rhs -> pred: Type0{true ==> pred};
  f_partial_cmp_post:v_Self -> v_Rhs -> t_Option t_Ordering -> Type0;
  f_partial_cmp:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure (t_Option t_Ordering)
        (f_partial_cmp_pre x0 x1)
        (fun result -> f_partial_cmp_post x0 x1 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) (v_Rhs:Type0) {|i: t_PartialOrd v_Self v_Rhs|} -> i._super_i0

/// See [`std::convert::TryInto`]
class t_TryInto (v_Self: Type0) (v_T: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Error:Type0;
  f_try_into_pre:self_: v_Self -> pred: Type0{true ==> pred};
  f_try_into_post:v_Self -> t_Result v_T f_Error -> Type0;
  f_try_into:x0: v_Self
    -> Prims.Pure (t_Result v_T f_Error)
        (f_try_into_pre x0)
        (fun result -> f_try_into_post x0 result)
}

/// See [`std::convert::TryFrom`]
class t_TryFrom (v_Self: Type0) (v_T: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Error:Type0;
  f_try_from_pre:x: v_T -> pred: Type0{true ==> pred};
  f_try_from_post:v_T -> t_Result v_Self f_Error -> Type0;
  f_try_from:x0: v_T
    -> Prims.Pure (t_Result v_Self f_Error)
        (f_try_from_pre x0)
        (fun result -> f_try_from_post x0 result)
}

/// See [`std::iter::Iterator`]
class t_Iterator (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Item:Type0;
  f_next_pre:self_: v_Self -> pred: Type0{true ==> pred};
  f_next_post:v_Self -> (v_Self & t_Option f_Item) -> Type0;
  f_next:x0: v_Self
    -> Prims.Pure (v_Self & t_Option f_Item) (f_next_pre x0) (fun result -> f_next_post x0 result)
}

/// See [`std::ops::IntoBounds`]
class t_IntoBounds (v_Self: Type0) (v_T: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:t_RangeBounds v_Self v_T;
  f_into_bounds_pre:self_: v_Self -> pred: Type0{true ==> pred};
  f_into_bounds_post:v_Self -> (t_Bound v_T & t_Bound v_T) -> Type0;
  f_into_bounds:x0: v_Self
    -> Prims.Pure (t_Bound v_T & t_Bound v_T)
        (f_into_bounds_pre x0)
        (fun result -> f_into_bounds_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) (v_T:Type0) {|i: t_IntoBounds v_Self v_T|} -> i._super_i0

/// See [`std::ops::OneSidedRange`]
class t_OneSidedRange (v_Self: Type0) (v_T: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:t_RangeBounds v_Self v_T;
  f_bound_pre:self_: v_Self -> pred: Type0{true ==> pred};
  f_bound_post:v_Self -> (t_OneSidedRangeBound & v_T) -> Type0;
  f_bound:x0: v_Self
    -> Prims.Pure (t_OneSidedRangeBound & v_T)
        (f_bound_pre x0)
        (fun result -> f_bound_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) (v_T:Type0) {|i: t_OneSidedRange v_Self v_T|} -> i._super_i0

/// See [`std::ops::Residual`]
class t_Residual (v_Self: Type0) (v_O: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_TryType:Type0;
  f_TryType_i0:t_Try f_TryType
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_T: Type0) (v_N: usize) : t_Iterator (t_IntoIter v_T v_N) =
  {
    f_Item = v_T;
    f_next_pre = (fun (self: t_IntoIter v_T v_N) -> true);
    f_next_post
    =
    (fun (self: t_IntoIter v_T v_N) (out1: (t_IntoIter v_T v_N & t_Option v_T)) -> true);
    f_next
    =
    fun (self: t_IntoIter v_T v_N) ->
      let (self: t_IntoIter v_T v_N), (hax_temp_output: t_Option v_T) =
        if (Rust_primitives.Sequence.seq_len #v_T self._0 <: usize) =. mk_usize 0
        then self, (Option_None <: t_Option v_T) <: (t_IntoIter v_T v_N & t_Option v_T)
        else
          let (tmp0: Rust_primitives.Sequence.t_Seq v_T), (out: v_T) =
            Rust_primitives.Sequence.seq_remove #v_T self._0 (mk_usize 0)
          in
          let self:t_IntoIter v_T v_N = { self with _0 = tmp0 } <: t_IntoIter v_T v_N in
          let res:v_T = out in
          self, (Option_Some res <: t_Option v_T) <: (t_IntoIter v_T v_N & t_Option v_T)
      in
      self, hax_temp_output <: (t_IntoIter v_T v_N & t_Option v_T)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2 (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_PartialOrd v_T v_T)
    : t_PartialOrd (t_Reverse v_T) (t_Reverse v_T) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_Reverse v_T) (other: t_Reverse v_T) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_Reverse v_T) (other: t_Reverse v_T) (out: t_Option t_Ordering) -> true);
    f_partial_cmp
    =
    fun (self: t_Reverse v_T) (other: t_Reverse v_T) ->
      f_partial_cmp #v_T #v_T #FStar.Tactics.Typeclasses.solve other._0 self._0
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_30: t_PartialOrd u8 u8 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: u8) (other: u8) -> true);
    f_partial_cmp_post
    =
    (fun (self_: u8) (other: u8) (res: t_Option t_Ordering) ->
        match res <: t_Option t_Ordering with
        | Option_Some (Ordering_Less ) -> self_ <. other
        | Option_Some (Ordering_Equal ) -> self_ =. other
        | Option_Some (Ordering_Greater ) -> self_ >. other
        | Option_None  -> false);
    f_partial_cmp
    =
    fun (self: u8) (other: u8) ->
      if self <. other
      then Option_Some (Ordering_Less <: t_Ordering) <: t_Option t_Ordering
      else
        if self >. other
        then Option_Some (Ordering_Greater <: t_Ordering) <: t_Option t_Ordering
        else Option_Some (Ordering_Equal <: t_Ordering) <: t_Option t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_32: t_PartialOrd i8 i8 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: i8) (other: i8) -> true);
    f_partial_cmp_post
    =
    (fun (self_: i8) (other: i8) (res: t_Option t_Ordering) ->
        match res <: t_Option t_Ordering with
        | Option_Some (Ordering_Less ) -> self_ <. other
        | Option_Some (Ordering_Equal ) -> self_ =. other
        | Option_Some (Ordering_Greater ) -> self_ >. other
        | Option_None  -> false);
    f_partial_cmp
    =
    fun (self: i8) (other: i8) ->
      if self <. other
      then Option_Some (Ordering_Less <: t_Ordering) <: t_Option t_Ordering
      else
        if self >. other
        then Option_Some (Ordering_Greater <: t_Ordering) <: t_Option t_Ordering
        else Option_Some (Ordering_Equal <: t_Ordering) <: t_Option t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_34: t_PartialOrd u16 u16 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: u16) (other: u16) -> true);
    f_partial_cmp_post
    =
    (fun (self_: u16) (other: u16) (res: t_Option t_Ordering) ->
        match res <: t_Option t_Ordering with
        | Option_Some (Ordering_Less ) -> self_ <. other
        | Option_Some (Ordering_Equal ) -> self_ =. other
        | Option_Some (Ordering_Greater ) -> self_ >. other
        | Option_None  -> false);
    f_partial_cmp
    =
    fun (self: u16) (other: u16) ->
      if self <. other
      then Option_Some (Ordering_Less <: t_Ordering) <: t_Option t_Ordering
      else
        if self >. other
        then Option_Some (Ordering_Greater <: t_Ordering) <: t_Option t_Ordering
        else Option_Some (Ordering_Equal <: t_Ordering) <: t_Option t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_36: t_PartialOrd i16 i16 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: i16) (other: i16) -> true);
    f_partial_cmp_post
    =
    (fun (self_: i16) (other: i16) (res: t_Option t_Ordering) ->
        match res <: t_Option t_Ordering with
        | Option_Some (Ordering_Less ) -> self_ <. other
        | Option_Some (Ordering_Equal ) -> self_ =. other
        | Option_Some (Ordering_Greater ) -> self_ >. other
        | Option_None  -> false);
    f_partial_cmp
    =
    fun (self: i16) (other: i16) ->
      if self <. other
      then Option_Some (Ordering_Less <: t_Ordering) <: t_Option t_Ordering
      else
        if self >. other
        then Option_Some (Ordering_Greater <: t_Ordering) <: t_Option t_Ordering
        else Option_Some (Ordering_Equal <: t_Ordering) <: t_Option t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_38: t_PartialOrd u32 u32 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: u32) (other: u32) -> true);
    f_partial_cmp_post
    =
    (fun (self_: u32) (other: u32) (res: t_Option t_Ordering) ->
        match res <: t_Option t_Ordering with
        | Option_Some (Ordering_Less ) -> self_ <. other
        | Option_Some (Ordering_Equal ) -> self_ =. other
        | Option_Some (Ordering_Greater ) -> self_ >. other
        | Option_None  -> false);
    f_partial_cmp
    =
    fun (self: u32) (other: u32) ->
      if self <. other
      then Option_Some (Ordering_Less <: t_Ordering) <: t_Option t_Ordering
      else
        if self >. other
        then Option_Some (Ordering_Greater <: t_Ordering) <: t_Option t_Ordering
        else Option_Some (Ordering_Equal <: t_Ordering) <: t_Option t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_40: t_PartialOrd i32 i32 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: i32) (other: i32) -> true);
    f_partial_cmp_post
    =
    (fun (self_: i32) (other: i32) (res: t_Option t_Ordering) ->
        match res <: t_Option t_Ordering with
        | Option_Some (Ordering_Less ) -> self_ <. other
        | Option_Some (Ordering_Equal ) -> self_ =. other
        | Option_Some (Ordering_Greater ) -> self_ >. other
        | Option_None  -> false);
    f_partial_cmp
    =
    fun (self: i32) (other: i32) ->
      if self <. other
      then Option_Some (Ordering_Less <: t_Ordering) <: t_Option t_Ordering
      else
        if self >. other
        then Option_Some (Ordering_Greater <: t_Ordering) <: t_Option t_Ordering
        else Option_Some (Ordering_Equal <: t_Ordering) <: t_Option t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_42: t_PartialOrd u64 u64 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: u64) (other: u64) -> true);
    f_partial_cmp_post
    =
    (fun (self_: u64) (other: u64) (res: t_Option t_Ordering) ->
        match res <: t_Option t_Ordering with
        | Option_Some (Ordering_Less ) -> self_ <. other
        | Option_Some (Ordering_Equal ) -> self_ =. other
        | Option_Some (Ordering_Greater ) -> self_ >. other
        | Option_None  -> false);
    f_partial_cmp
    =
    fun (self: u64) (other: u64) ->
      if self <. other
      then Option_Some (Ordering_Less <: t_Ordering) <: t_Option t_Ordering
      else
        if self >. other
        then Option_Some (Ordering_Greater <: t_Ordering) <: t_Option t_Ordering
        else Option_Some (Ordering_Equal <: t_Ordering) <: t_Option t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_44: t_PartialOrd i64 i64 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: i64) (other: i64) -> true);
    f_partial_cmp_post
    =
    (fun (self_: i64) (other: i64) (res: t_Option t_Ordering) ->
        match res <: t_Option t_Ordering with
        | Option_Some (Ordering_Less ) -> self_ <. other
        | Option_Some (Ordering_Equal ) -> self_ =. other
        | Option_Some (Ordering_Greater ) -> self_ >. other
        | Option_None  -> false);
    f_partial_cmp
    =
    fun (self: i64) (other: i64) ->
      if self <. other
      then Option_Some (Ordering_Less <: t_Ordering) <: t_Option t_Ordering
      else
        if self >. other
        then Option_Some (Ordering_Greater <: t_Ordering) <: t_Option t_Ordering
        else Option_Some (Ordering_Equal <: t_Ordering) <: t_Option t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_46: t_PartialOrd u128 u128 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: u128) (other: u128) -> true);
    f_partial_cmp_post
    =
    (fun (self_: u128) (other: u128) (res: t_Option t_Ordering) ->
        match res <: t_Option t_Ordering with
        | Option_Some (Ordering_Less ) -> self_ <. other
        | Option_Some (Ordering_Equal ) -> self_ =. other
        | Option_Some (Ordering_Greater ) -> self_ >. other
        | Option_None  -> false);
    f_partial_cmp
    =
    fun (self: u128) (other: u128) ->
      if self <. other
      then Option_Some (Ordering_Less <: t_Ordering) <: t_Option t_Ordering
      else
        if self >. other
        then Option_Some (Ordering_Greater <: t_Ordering) <: t_Option t_Ordering
        else Option_Some (Ordering_Equal <: t_Ordering) <: t_Option t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_48: t_PartialOrd i128 i128 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: i128) (other: i128) -> true);
    f_partial_cmp_post
    =
    (fun (self_: i128) (other: i128) (res: t_Option t_Ordering) ->
        match res <: t_Option t_Ordering with
        | Option_Some (Ordering_Less ) -> self_ <. other
        | Option_Some (Ordering_Equal ) -> self_ =. other
        | Option_Some (Ordering_Greater ) -> self_ >. other
        | Option_None  -> false);
    f_partial_cmp
    =
    fun (self: i128) (other: i128) ->
      if self <. other
      then Option_Some (Ordering_Less <: t_Ordering) <: t_Option t_Ordering
      else
        if self >. other
        then Option_Some (Ordering_Greater <: t_Ordering) <: t_Option t_Ordering
        else Option_Some (Ordering_Equal <: t_Ordering) <: t_Option t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_50: t_PartialOrd usize usize =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: usize) (other: usize) -> true);
    f_partial_cmp_post
    =
    (fun (self_: usize) (other: usize) (res: t_Option t_Ordering) ->
        match res <: t_Option t_Ordering with
        | Option_Some (Ordering_Less ) -> self_ <. other
        | Option_Some (Ordering_Equal ) -> self_ =. other
        | Option_Some (Ordering_Greater ) -> self_ >. other
        | Option_None  -> false);
    f_partial_cmp
    =
    fun (self: usize) (other: usize) ->
      if self <. other
      then Option_Some (Ordering_Less <: t_Ordering) <: t_Option t_Ordering
      else
        if self >. other
        then Option_Some (Ordering_Greater <: t_Ordering) <: t_Option t_Ordering
        else Option_Some (Ordering_Equal <: t_Ordering) <: t_Option t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_52: t_PartialOrd isize isize =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: isize) (other: isize) -> true);
    f_partial_cmp_post
    =
    (fun (self_: isize) (other: isize) (res: t_Option t_Ordering) ->
        match res <: t_Option t_Ordering with
        | Option_Some (Ordering_Less ) -> self_ <. other
        | Option_Some (Ordering_Equal ) -> self_ =. other
        | Option_Some (Ordering_Greater ) -> self_ >. other
        | Option_None  -> false);
    f_partial_cmp
    =
    fun (self: isize) (other: isize) ->
      if self <. other
      then Option_Some (Ordering_Less <: t_Ordering) <: t_Option t_Ordering
      else
        if self >. other
        then Option_Some (Ordering_Greater <: t_Ordering) <: t_Option t_Ordering
        else Option_Some (Ordering_Equal <: t_Ordering) <: t_Option t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1__from__convert
      (#v_T #v_U: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_From v_U v_T)
    : t_TryFrom v_U v_T =
  {
    f_Error = t_Infallible;
    f_try_from_pre = (fun (x: v_T) -> true);
    f_try_from_post = (fun (x: v_T) (out: t_Result v_U t_Infallible) -> true);
    f_try_from
    =
    fun (x: v_T) ->
      Result_Ok (f_from #v_U #v_T #FStar.Tactics.Typeclasses.solve x) <: t_Result v_U t_Infallible
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2__from__convert
      (#v_T: Type0)
      (v_N: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Marker.t_Copy v_T)
    : t_TryFrom (t_Array v_T v_N) (t_Slice v_T) =
  {
    f_Error = t_TryFromSliceError;
    f_try_from_pre = (fun (x: t_Slice v_T) -> true);
    f_try_from_post
    =
    (fun (x: t_Slice v_T) (out: t_Result (t_Array v_T v_N) t_TryFromSliceError) -> true);
    f_try_from
    =
    fun (x: t_Slice v_T) ->
      if (Rust_primitives.Slice.slice_length #v_T x <: usize) =. v_N
      then
        Result_Ok
        (Rust_primitives.Slice.array_from_fn #v_T
            v_N
            #(usize -> v_T)
            (fun i ->
                let i:usize = i in
                Rust_primitives.Slice.slice_index #v_T x i <: v_T))
        <:
        t_Result (t_Array v_T v_N) t_TryFromSliceError
      else
        Result_Err (TryFromSliceError <: t_TryFromSliceError)
        <:
        t_Result (t_Array v_T v_N) t_TryFromSliceError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3__from__convert
      (#v_T #v_U: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_TryFrom v_U v_T)
    : t_TryInto v_T v_U =
  {
    f_Error = i0.f_Error;
    f_try_into_pre = (fun (self: v_T) -> true);
    f_try_into_post = (fun (self: v_T) (out: t_Result v_U i0.f_Error) -> true);
    f_try_into = fun (self: v_T) -> f_try_from #v_U #v_T #FStar.Tactics.Typeclasses.solve self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_41: t_TryFrom u8 u16 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: u16) -> true);
    f_try_from_post
    =
    (fun (x: u16) (out: t_Result u8 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: u16) ->
      if x >. (cast (impl_6__MAX <: u8) <: u16) || x <. (cast (impl_6__MIN <: u8) <: u16)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u8 Core_models.Num.Error.t_TryFromIntError
      else Result_Ok (cast (x <: u16) <: u8) <: t_Result u8 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_42__from__convert: t_TryFrom u8 u32 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: u32) -> true);
    f_try_from_post
    =
    (fun (x: u32) (out: t_Result u8 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: u32) ->
      if x >. (cast (impl_6__MAX <: u8) <: u32) || x <. (cast (impl_6__MIN <: u8) <: u32)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u8 Core_models.Num.Error.t_TryFromIntError
      else Result_Ok (cast (x <: u32) <: u8) <: t_Result u8 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_43: t_TryFrom u16 u32 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: u32) -> true);
    f_try_from_post
    =
    (fun (x: u32) (out: t_Result u16 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: u32) ->
      if x >. (cast (impl_7__MAX <: u16) <: u32) || x <. (cast (impl_7__MIN <: u16) <: u32)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u16 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: u32) <: u16) <: t_Result u16 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_44__from__convert: t_TryFrom u8 u64 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: u64) -> true);
    f_try_from_post
    =
    (fun (x: u64) (out: t_Result u8 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: u64) ->
      if x >. (cast (impl_6__MAX <: u8) <: u64) || x <. (cast (impl_6__MIN <: u8) <: u64)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u8 Core_models.Num.Error.t_TryFromIntError
      else Result_Ok (cast (x <: u64) <: u8) <: t_Result u8 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_45: t_TryFrom u16 u64 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: u64) -> true);
    f_try_from_post
    =
    (fun (x: u64) (out: t_Result u16 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: u64) ->
      if x >. (cast (impl_7__MAX <: u16) <: u64) || x <. (cast (impl_7__MIN <: u16) <: u64)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u16 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: u64) <: u16) <: t_Result u16 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_46__from__convert: t_TryFrom u32 u64 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: u64) -> true);
    f_try_from_post
    =
    (fun (x: u64) (out: t_Result u32 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: u64) ->
      if x >. (cast (impl_8__MAX <: u32) <: u64) || x <. (cast (impl_8__MIN <: u32) <: u64)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u32 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: u64) <: u32) <: t_Result u32 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_47: t_TryFrom usize u64 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: u64) -> true);
    f_try_from_post
    =
    (fun (x: u64) (out: t_Result usize Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: u64) ->
      if x >. (cast (impl_11__MAX <: usize) <: u64) || x <. (cast (impl_11__MIN <: usize) <: u64)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result usize Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: u64) <: usize)
        <:
        t_Result usize Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_48__from__convert: t_TryFrom u8 u128 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: u128) -> true);
    f_try_from_post
    =
    (fun (x: u128) (out: t_Result u8 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: u128) ->
      if x >. (cast (impl_6__MAX <: u8) <: u128) || x <. (cast (impl_6__MIN <: u8) <: u128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u8 Core_models.Num.Error.t_TryFromIntError
      else Result_Ok (cast (x <: u128) <: u8) <: t_Result u8 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_49: t_TryFrom u16 u128 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: u128) -> true);
    f_try_from_post
    =
    (fun (x: u128) (out: t_Result u16 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: u128) ->
      if x >. (cast (impl_7__MAX <: u16) <: u128) || x <. (cast (impl_7__MIN <: u16) <: u128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u16 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: u128) <: u16) <: t_Result u16 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_50__from__convert: t_TryFrom u32 u128 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: u128) -> true);
    f_try_from_post
    =
    (fun (x: u128) (out: t_Result u32 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: u128) ->
      if x >. (cast (impl_8__MAX <: u32) <: u128) || x <. (cast (impl_8__MIN <: u32) <: u128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u32 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: u128) <: u32) <: t_Result u32 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_51: t_TryFrom u64 u128 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: u128) -> true);
    f_try_from_post
    =
    (fun (x: u128) (out: t_Result u64 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: u128) ->
      if x >. (cast (impl_9__MAX <: u64) <: u128) || x <. (cast (impl_9__MIN <: u64) <: u128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u64 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: u128) <: u64) <: t_Result u64 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_52__from__convert: t_TryFrom usize u128 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: u128) -> true);
    f_try_from_post
    =
    (fun (x: u128) (out: t_Result usize Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: u128) ->
      if x >. (cast (impl_11__MAX <: usize) <: u128) || x <. (cast (impl_11__MIN <: usize) <: u128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result usize Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: u128) <: usize)
        <:
        t_Result usize Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_53: t_TryFrom u8 usize =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: usize) -> true);
    f_try_from_post
    =
    (fun (x: usize) (out: t_Result u8 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: usize) ->
      if x >. (cast (impl_6__MAX <: u8) <: usize) || x <. (cast (impl_6__MIN <: u8) <: usize)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u8 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: usize) <: u8) <: t_Result u8 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_54: t_TryFrom u16 usize =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: usize) -> true);
    f_try_from_post
    =
    (fun (x: usize) (out: t_Result u16 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: usize) ->
      if x >. (cast (impl_7__MAX <: u16) <: usize) || x <. (cast (impl_7__MIN <: u16) <: usize)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u16 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: usize) <: u16) <: t_Result u16 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_55: t_TryFrom u32 usize =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: usize) -> true);
    f_try_from_post
    =
    (fun (x: usize) (out: t_Result u32 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: usize) ->
      if x >. (cast (impl_8__MAX <: u32) <: usize) || x <. (cast (impl_8__MIN <: u32) <: usize)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u32 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: usize) <: u32) <: t_Result u32 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_56: t_TryFrom u64 usize =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: usize) -> true);
    f_try_from_post
    =
    (fun (x: usize) (out: t_Result u64 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: usize) ->
      if x >. (cast (impl_9__MAX <: u64) <: usize) || x <. (cast (impl_9__MIN <: u64) <: usize)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u64 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: usize) <: u64) <: t_Result u64 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_57: t_TryFrom i8 i16 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i16) -> true);
    f_try_from_post
    =
    (fun (x: i16) (out: t_Result i8 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i16) ->
      if x >. (cast (impl_12__MAX <: i8) <: i16) || x <. (cast (impl_12__MIN <: i8) <: i16)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result i8 Core_models.Num.Error.t_TryFromIntError
      else Result_Ok (cast (x <: i16) <: i8) <: t_Result i8 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_58: t_TryFrom i8 i32 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i32) -> true);
    f_try_from_post
    =
    (fun (x: i32) (out: t_Result i8 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i32) ->
      if x >. (cast (impl_12__MAX <: i8) <: i32) || x <. (cast (impl_12__MIN <: i8) <: i32)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result i8 Core_models.Num.Error.t_TryFromIntError
      else Result_Ok (cast (x <: i32) <: i8) <: t_Result i8 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_59: t_TryFrom i16 i32 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i32) -> true);
    f_try_from_post
    =
    (fun (x: i32) (out: t_Result i16 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i32) ->
      if x >. (cast (impl_13__MAX <: i16) <: i32) || x <. (cast (impl_13__MIN <: i16) <: i32)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result i16 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: i32) <: i16) <: t_Result i16 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_60: t_TryFrom i8 i64 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i64) -> true);
    f_try_from_post
    =
    (fun (x: i64) (out: t_Result i8 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i64) ->
      if x >. (cast (impl_12__MAX <: i8) <: i64) || x <. (cast (impl_12__MIN <: i8) <: i64)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result i8 Core_models.Num.Error.t_TryFromIntError
      else Result_Ok (cast (x <: i64) <: i8) <: t_Result i8 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_61: t_TryFrom i16 i64 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i64) -> true);
    f_try_from_post
    =
    (fun (x: i64) (out: t_Result i16 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i64) ->
      if x >. (cast (impl_13__MAX <: i16) <: i64) || x <. (cast (impl_13__MIN <: i16) <: i64)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result i16 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: i64) <: i16) <: t_Result i16 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_62: t_TryFrom i32 i64 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i64) -> true);
    f_try_from_post
    =
    (fun (x: i64) (out: t_Result i32 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i64) ->
      if x >. (cast (impl_14__MAX <: i32) <: i64) || x <. (cast (impl_14__MIN <: i32) <: i64)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result i32 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: i64) <: i32) <: t_Result i32 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_63: t_TryFrom isize i64 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i64) -> true);
    f_try_from_post
    =
    (fun (x: i64) (out: t_Result isize Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i64) ->
      if x >. (cast (impl_17__MAX <: isize) <: i64) || x <. (cast (impl_17__MIN <: isize) <: i64)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result isize Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: i64) <: isize)
        <:
        t_Result isize Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_64: t_TryFrom i8 i128 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i128) -> true);
    f_try_from_post
    =
    (fun (x: i128) (out: t_Result i8 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i128) ->
      if x >. (cast (impl_12__MAX <: i8) <: i128) || x <. (cast (impl_12__MIN <: i8) <: i128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result i8 Core_models.Num.Error.t_TryFromIntError
      else Result_Ok (cast (x <: i128) <: i8) <: t_Result i8 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_65: t_TryFrom i16 i128 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i128) -> true);
    f_try_from_post
    =
    (fun (x: i128) (out: t_Result i16 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i128) ->
      if x >. (cast (impl_13__MAX <: i16) <: i128) || x <. (cast (impl_13__MIN <: i16) <: i128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result i16 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: i128) <: i16) <: t_Result i16 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_66: t_TryFrom i32 i128 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i128) -> true);
    f_try_from_post
    =
    (fun (x: i128) (out: t_Result i32 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i128) ->
      if x >. (cast (impl_14__MAX <: i32) <: i128) || x <. (cast (impl_14__MIN <: i32) <: i128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result i32 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: i128) <: i32) <: t_Result i32 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_67: t_TryFrom i64 i128 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i128) -> true);
    f_try_from_post
    =
    (fun (x: i128) (out: t_Result i64 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i128) ->
      if x >. (cast (impl_15__MAX <: i64) <: i128) || x <. (cast (impl_15__MIN <: i64) <: i128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result i64 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: i128) <: i64) <: t_Result i64 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_68: t_TryFrom isize i128 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i128) -> true);
    f_try_from_post
    =
    (fun (x: i128) (out: t_Result isize Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i128) ->
      if x >. (cast (impl_17__MAX <: isize) <: i128) || x <. (cast (impl_17__MIN <: isize) <: i128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result isize Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: i128) <: isize)
        <:
        t_Result isize Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_69: t_TryFrom i8 isize =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: isize) -> true);
    f_try_from_post
    =
    (fun (x: isize) (out: t_Result i8 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: isize) ->
      if x >. (cast (impl_12__MAX <: i8) <: isize) || x <. (cast (impl_12__MIN <: i8) <: isize)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result i8 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: isize) <: i8) <: t_Result i8 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_70: t_TryFrom i16 isize =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: isize) -> true);
    f_try_from_post
    =
    (fun (x: isize) (out: t_Result i16 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: isize) ->
      if x >. (cast (impl_13__MAX <: i16) <: isize) || x <. (cast (impl_13__MIN <: i16) <: isize)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result i16 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: isize) <: i16) <: t_Result i16 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_71: t_TryFrom i32 isize =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: isize) -> true);
    f_try_from_post
    =
    (fun (x: isize) (out: t_Result i32 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: isize) ->
      if x >. (cast (impl_14__MAX <: i32) <: isize) || x <. (cast (impl_14__MIN <: i32) <: isize)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result i32 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: isize) <: i32) <: t_Result i32 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_72: t_TryFrom i64 isize =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: isize) -> true);
    f_try_from_post
    =
    (fun (x: isize) (out: t_Result i64 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: isize) ->
      if x >. (cast (impl_15__MAX <: i64) <: isize) || x <. (cast (impl_15__MIN <: i64) <: isize)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result i64 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: isize) <: i64) <: t_Result i64 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_73: t_TryFrom isize i32 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i32) -> true);
    f_try_from_post
    =
    (fun (x: i32) (out: t_Result isize Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i32) ->
      Result_Ok (cast (x <: i32) <: isize) <: t_Result isize Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_74: t_TryFrom i128 isize =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: isize) -> true);
    f_try_from_post
    =
    (fun (x: isize) (out: t_Result i128 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: isize) ->
      Result_Ok (cast (x <: isize) <: i128) <: t_Result i128 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_75: t_TryFrom usize u32 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: u32) -> true);
    f_try_from_post
    =
    (fun (x: u32) (out: t_Result usize Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: u32) ->
      Result_Ok (cast (x <: u32) <: usize) <: t_Result usize Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_76: t_TryFrom u128 usize =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: usize) -> true);
    f_try_from_post
    =
    (fun (x: usize) (out: t_Result u128 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: usize) ->
      Result_Ok (cast (x <: usize) <: u128) <: t_Result u128 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_77: t_TryFrom i8 u8 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: u8) -> true);
    f_try_from_post
    =
    (fun (x: u8) (out: t_Result i8 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: u8) ->
      if x >. (cast (impl_12__MAX <: i8) <: u8)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result i8 Core_models.Num.Error.t_TryFromIntError
      else Result_Ok (cast (x <: u8) <: i8) <: t_Result i8 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_78: t_TryFrom i8 u16 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: u16) -> true);
    f_try_from_post
    =
    (fun (x: u16) (out: t_Result i8 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: u16) ->
      if x >. (cast (impl_12__MAX <: i8) <: u16)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result i8 Core_models.Num.Error.t_TryFromIntError
      else Result_Ok (cast (x <: u16) <: i8) <: t_Result i8 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_79: t_TryFrom i16 u16 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: u16) -> true);
    f_try_from_post
    =
    (fun (x: u16) (out: t_Result i16 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: u16) ->
      if x >. (cast (impl_13__MAX <: i16) <: u16)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result i16 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: u16) <: i16) <: t_Result i16 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_80: t_TryFrom i8 u32 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: u32) -> true);
    f_try_from_post
    =
    (fun (x: u32) (out: t_Result i8 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: u32) ->
      if x >. (cast (impl_12__MAX <: i8) <: u32)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result i8 Core_models.Num.Error.t_TryFromIntError
      else Result_Ok (cast (x <: u32) <: i8) <: t_Result i8 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_81: t_TryFrom i16 u32 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: u32) -> true);
    f_try_from_post
    =
    (fun (x: u32) (out: t_Result i16 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: u32) ->
      if x >. (cast (impl_13__MAX <: i16) <: u32)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result i16 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: u32) <: i16) <: t_Result i16 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_82: t_TryFrom i32 u32 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: u32) -> true);
    f_try_from_post
    =
    (fun (x: u32) (out: t_Result i32 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: u32) ->
      if x >. (cast (impl_14__MAX <: i32) <: u32)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result i32 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: u32) <: i32) <: t_Result i32 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_83: t_TryFrom i8 u64 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: u64) -> true);
    f_try_from_post
    =
    (fun (x: u64) (out: t_Result i8 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: u64) ->
      if x >. (cast (impl_12__MAX <: i8) <: u64)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result i8 Core_models.Num.Error.t_TryFromIntError
      else Result_Ok (cast (x <: u64) <: i8) <: t_Result i8 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_84: t_TryFrom i16 u64 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: u64) -> true);
    f_try_from_post
    =
    (fun (x: u64) (out: t_Result i16 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: u64) ->
      if x >. (cast (impl_13__MAX <: i16) <: u64)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result i16 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: u64) <: i16) <: t_Result i16 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_85: t_TryFrom i32 u64 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: u64) -> true);
    f_try_from_post
    =
    (fun (x: u64) (out: t_Result i32 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: u64) ->
      if x >. (cast (impl_14__MAX <: i32) <: u64)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result i32 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: u64) <: i32) <: t_Result i32 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_86: t_TryFrom i64 u64 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: u64) -> true);
    f_try_from_post
    =
    (fun (x: u64) (out: t_Result i64 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: u64) ->
      if x >. (cast (impl_15__MAX <: i64) <: u64)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result i64 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: u64) <: i64) <: t_Result i64 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_87: t_TryFrom i8 u128 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: u128) -> true);
    f_try_from_post
    =
    (fun (x: u128) (out: t_Result i8 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: u128) ->
      if x >. (cast (impl_12__MAX <: i8) <: u128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result i8 Core_models.Num.Error.t_TryFromIntError
      else Result_Ok (cast (x <: u128) <: i8) <: t_Result i8 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_88: t_TryFrom i16 u128 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: u128) -> true);
    f_try_from_post
    =
    (fun (x: u128) (out: t_Result i16 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: u128) ->
      if x >. (cast (impl_13__MAX <: i16) <: u128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result i16 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: u128) <: i16) <: t_Result i16 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_89: t_TryFrom i32 u128 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: u128) -> true);
    f_try_from_post
    =
    (fun (x: u128) (out: t_Result i32 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: u128) ->
      if x >. (cast (impl_14__MAX <: i32) <: u128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result i32 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: u128) <: i32) <: t_Result i32 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_90: t_TryFrom i64 u128 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: u128) -> true);
    f_try_from_post
    =
    (fun (x: u128) (out: t_Result i64 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: u128) ->
      if x >. (cast (impl_15__MAX <: i64) <: u128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result i64 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: u128) <: i64) <: t_Result i64 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_91: t_TryFrom i128 u128 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: u128) -> true);
    f_try_from_post
    =
    (fun (x: u128) (out: t_Result i128 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: u128) ->
      if x >. (cast (impl_16__MAX <: i128) <: u128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result i128 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: u128) <: i128)
        <:
        t_Result i128 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_92: t_TryFrom i8 usize =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: usize) -> true);
    f_try_from_post
    =
    (fun (x: usize) (out: t_Result i8 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: usize) ->
      if x >. (cast (impl_12__MAX <: i8) <: usize)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result i8 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: usize) <: i8) <: t_Result i8 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_93: t_TryFrom i16 usize =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: usize) -> true);
    f_try_from_post
    =
    (fun (x: usize) (out: t_Result i16 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: usize) ->
      if x >. (cast (impl_13__MAX <: i16) <: usize)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result i16 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: usize) <: i16) <: t_Result i16 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_94: t_TryFrom i32 usize =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: usize) -> true);
    f_try_from_post
    =
    (fun (x: usize) (out: t_Result i32 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: usize) ->
      if x >. (cast (impl_14__MAX <: i32) <: usize)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result i32 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: usize) <: i32) <: t_Result i32 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_95: t_TryFrom i64 usize =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: usize) -> true);
    f_try_from_post
    =
    (fun (x: usize) (out: t_Result i64 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: usize) ->
      if x >. (cast (impl_15__MAX <: i64) <: usize)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result i64 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: usize) <: i64) <: t_Result i64 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_96: t_TryFrom isize usize =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: usize) -> true);
    f_try_from_post
    =
    (fun (x: usize) (out: t_Result isize Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: usize) ->
      if x >. (cast (impl_17__MAX <: isize) <: usize)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result isize Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: usize) <: isize)
        <:
        t_Result isize Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_97: t_TryFrom u8 i8 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i8) -> true);
    f_try_from_post
    =
    (fun (x: i8) (out: t_Result u8 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i8) ->
      if x <. mk_i8 0 || (cast (x <: i8) <: u128) >. (cast (impl_6__MAX <: u8) <: u128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u8 Core_models.Num.Error.t_TryFromIntError
      else Result_Ok (cast (x <: i8) <: u8) <: t_Result u8 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_98: t_TryFrom u16 i8 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i8) -> true);
    f_try_from_post
    =
    (fun (x: i8) (out: t_Result u16 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i8) ->
      if x <. mk_i8 0 || (cast (x <: i8) <: u128) >. (cast (impl_7__MAX <: u16) <: u128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u16 Core_models.Num.Error.t_TryFromIntError
      else Result_Ok (cast (x <: i8) <: u16) <: t_Result u16 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_99: t_TryFrom u32 i8 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i8) -> true);
    f_try_from_post
    =
    (fun (x: i8) (out: t_Result u32 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i8) ->
      if x <. mk_i8 0 || (cast (x <: i8) <: u128) >. (cast (impl_8__MAX <: u32) <: u128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u32 Core_models.Num.Error.t_TryFromIntError
      else Result_Ok (cast (x <: i8) <: u32) <: t_Result u32 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_100: t_TryFrom u64 i8 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i8) -> true);
    f_try_from_post
    =
    (fun (x: i8) (out: t_Result u64 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i8) ->
      if x <. mk_i8 0 || (cast (x <: i8) <: u128) >. (cast (impl_9__MAX <: u64) <: u128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u64 Core_models.Num.Error.t_TryFromIntError
      else Result_Ok (cast (x <: i8) <: u64) <: t_Result u64 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_101: t_TryFrom u128 i8 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i8) -> true);
    f_try_from_post
    =
    (fun (x: i8) (out: t_Result u128 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i8) ->
      if x <. mk_i8 0 || (cast (x <: i8) <: u128) >. impl_10__MAX
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u128 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: i8) <: u128) <: t_Result u128 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_102: t_TryFrom usize i8 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i8) -> true);
    f_try_from_post
    =
    (fun (x: i8) (out: t_Result usize Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i8) ->
      if x <. mk_i8 0 || (cast (x <: i8) <: u128) >. (cast (impl_11__MAX <: usize) <: u128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result usize Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: i8) <: usize)
        <:
        t_Result usize Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_103: t_TryFrom u8 i16 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i16) -> true);
    f_try_from_post
    =
    (fun (x: i16) (out: t_Result u8 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i16) ->
      if x <. mk_i16 0 || (cast (x <: i16) <: u128) >. (cast (impl_6__MAX <: u8) <: u128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u8 Core_models.Num.Error.t_TryFromIntError
      else Result_Ok (cast (x <: i16) <: u8) <: t_Result u8 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_104: t_TryFrom u16 i16 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i16) -> true);
    f_try_from_post
    =
    (fun (x: i16) (out: t_Result u16 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i16) ->
      if x <. mk_i16 0 || (cast (x <: i16) <: u128) >. (cast (impl_7__MAX <: u16) <: u128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u16 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: i16) <: u16) <: t_Result u16 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_105: t_TryFrom u32 i16 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i16) -> true);
    f_try_from_post
    =
    (fun (x: i16) (out: t_Result u32 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i16) ->
      if x <. mk_i16 0 || (cast (x <: i16) <: u128) >. (cast (impl_8__MAX <: u32) <: u128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u32 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: i16) <: u32) <: t_Result u32 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_106: t_TryFrom u64 i16 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i16) -> true);
    f_try_from_post
    =
    (fun (x: i16) (out: t_Result u64 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i16) ->
      if x <. mk_i16 0 || (cast (x <: i16) <: u128) >. (cast (impl_9__MAX <: u64) <: u128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u64 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: i16) <: u64) <: t_Result u64 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_107: t_TryFrom u128 i16 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i16) -> true);
    f_try_from_post
    =
    (fun (x: i16) (out: t_Result u128 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i16) ->
      if x <. mk_i16 0 || (cast (x <: i16) <: u128) >. impl_10__MAX
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u128 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: i16) <: u128) <: t_Result u128 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_108: t_TryFrom usize i16 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i16) -> true);
    f_try_from_post
    =
    (fun (x: i16) (out: t_Result usize Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i16) ->
      if x <. mk_i16 0 || (cast (x <: i16) <: u128) >. (cast (impl_11__MAX <: usize) <: u128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result usize Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: i16) <: usize)
        <:
        t_Result usize Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_109: t_TryFrom u8 i32 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i32) -> true);
    f_try_from_post
    =
    (fun (x: i32) (out: t_Result u8 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i32) ->
      if x <. mk_i32 0 || (cast (x <: i32) <: u128) >. (cast (impl_6__MAX <: u8) <: u128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u8 Core_models.Num.Error.t_TryFromIntError
      else Result_Ok (cast (x <: i32) <: u8) <: t_Result u8 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_110: t_TryFrom u16 i32 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i32) -> true);
    f_try_from_post
    =
    (fun (x: i32) (out: t_Result u16 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i32) ->
      if x <. mk_i32 0 || (cast (x <: i32) <: u128) >. (cast (impl_7__MAX <: u16) <: u128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u16 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: i32) <: u16) <: t_Result u16 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_111: t_TryFrom u32 i32 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i32) -> true);
    f_try_from_post
    =
    (fun (x: i32) (out: t_Result u32 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i32) ->
      if x <. mk_i32 0 || (cast (x <: i32) <: u128) >. (cast (impl_8__MAX <: u32) <: u128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u32 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: i32) <: u32) <: t_Result u32 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_112: t_TryFrom u64 i32 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i32) -> true);
    f_try_from_post
    =
    (fun (x: i32) (out: t_Result u64 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i32) ->
      if x <. mk_i32 0 || (cast (x <: i32) <: u128) >. (cast (impl_9__MAX <: u64) <: u128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u64 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: i32) <: u64) <: t_Result u64 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_113: t_TryFrom u128 i32 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i32) -> true);
    f_try_from_post
    =
    (fun (x: i32) (out: t_Result u128 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i32) ->
      if x <. mk_i32 0 || (cast (x <: i32) <: u128) >. impl_10__MAX
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u128 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: i32) <: u128) <: t_Result u128 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_114: t_TryFrom usize i32 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i32) -> true);
    f_try_from_post
    =
    (fun (x: i32) (out: t_Result usize Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i32) ->
      if x <. mk_i32 0 || (cast (x <: i32) <: u128) >. (cast (impl_11__MAX <: usize) <: u128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result usize Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: i32) <: usize)
        <:
        t_Result usize Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_115: t_TryFrom u8 i64 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i64) -> true);
    f_try_from_post
    =
    (fun (x: i64) (out: t_Result u8 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i64) ->
      if x <. mk_i64 0 || (cast (x <: i64) <: u128) >. (cast (impl_6__MAX <: u8) <: u128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u8 Core_models.Num.Error.t_TryFromIntError
      else Result_Ok (cast (x <: i64) <: u8) <: t_Result u8 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_116: t_TryFrom u16 i64 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i64) -> true);
    f_try_from_post
    =
    (fun (x: i64) (out: t_Result u16 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i64) ->
      if x <. mk_i64 0 || (cast (x <: i64) <: u128) >. (cast (impl_7__MAX <: u16) <: u128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u16 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: i64) <: u16) <: t_Result u16 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_117: t_TryFrom u32 i64 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i64) -> true);
    f_try_from_post
    =
    (fun (x: i64) (out: t_Result u32 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i64) ->
      if x <. mk_i64 0 || (cast (x <: i64) <: u128) >. (cast (impl_8__MAX <: u32) <: u128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u32 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: i64) <: u32) <: t_Result u32 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_118: t_TryFrom u64 i64 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i64) -> true);
    f_try_from_post
    =
    (fun (x: i64) (out: t_Result u64 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i64) ->
      if x <. mk_i64 0 || (cast (x <: i64) <: u128) >. (cast (impl_9__MAX <: u64) <: u128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u64 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: i64) <: u64) <: t_Result u64 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_119: t_TryFrom u128 i64 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i64) -> true);
    f_try_from_post
    =
    (fun (x: i64) (out: t_Result u128 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i64) ->
      if x <. mk_i64 0 || (cast (x <: i64) <: u128) >. impl_10__MAX
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u128 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: i64) <: u128) <: t_Result u128 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_120: t_TryFrom usize i64 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i64) -> true);
    f_try_from_post
    =
    (fun (x: i64) (out: t_Result usize Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i64) ->
      if x <. mk_i64 0 || (cast (x <: i64) <: u128) >. (cast (impl_11__MAX <: usize) <: u128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result usize Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: i64) <: usize)
        <:
        t_Result usize Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_121: t_TryFrom u8 i128 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i128) -> true);
    f_try_from_post
    =
    (fun (x: i128) (out: t_Result u8 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i128) ->
      if x <. mk_i128 0 || (cast (x <: i128) <: u128) >. (cast (impl_6__MAX <: u8) <: u128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u8 Core_models.Num.Error.t_TryFromIntError
      else Result_Ok (cast (x <: i128) <: u8) <: t_Result u8 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_122: t_TryFrom u16 i128 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i128) -> true);
    f_try_from_post
    =
    (fun (x: i128) (out: t_Result u16 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i128) ->
      if x <. mk_i128 0 || (cast (x <: i128) <: u128) >. (cast (impl_7__MAX <: u16) <: u128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u16 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: i128) <: u16) <: t_Result u16 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_123: t_TryFrom u32 i128 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i128) -> true);
    f_try_from_post
    =
    (fun (x: i128) (out: t_Result u32 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i128) ->
      if x <. mk_i128 0 || (cast (x <: i128) <: u128) >. (cast (impl_8__MAX <: u32) <: u128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u32 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: i128) <: u32) <: t_Result u32 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_124: t_TryFrom u64 i128 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i128) -> true);
    f_try_from_post
    =
    (fun (x: i128) (out: t_Result u64 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i128) ->
      if x <. mk_i128 0 || (cast (x <: i128) <: u128) >. (cast (impl_9__MAX <: u64) <: u128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u64 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: i128) <: u64) <: t_Result u64 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_125: t_TryFrom u128 i128 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i128) -> true);
    f_try_from_post
    =
    (fun (x: i128) (out: t_Result u128 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i128) ->
      if x <. mk_i128 0 || (cast (x <: i128) <: u128) >. impl_10__MAX
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u128 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: i128) <: u128)
        <:
        t_Result u128 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_126: t_TryFrom usize i128 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i128) -> true);
    f_try_from_post
    =
    (fun (x: i128) (out: t_Result usize Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: i128) ->
      if x <. mk_i128 0 || (cast (x <: i128) <: u128) >. (cast (impl_11__MAX <: usize) <: u128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result usize Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: i128) <: usize)
        <:
        t_Result usize Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_127: t_TryFrom u8 isize =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: isize) -> true);
    f_try_from_post
    =
    (fun (x: isize) (out: t_Result u8 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: isize) ->
      if x <. mk_isize 0 || (cast (x <: isize) <: u128) >. (cast (impl_6__MAX <: u8) <: u128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u8 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: isize) <: u8) <: t_Result u8 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_128: t_TryFrom u16 isize =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: isize) -> true);
    f_try_from_post
    =
    (fun (x: isize) (out: t_Result u16 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: isize) ->
      if x <. mk_isize 0 || (cast (x <: isize) <: u128) >. (cast (impl_7__MAX <: u16) <: u128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u16 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: isize) <: u16) <: t_Result u16 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_129: t_TryFrom u32 isize =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: isize) -> true);
    f_try_from_post
    =
    (fun (x: isize) (out: t_Result u32 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: isize) ->
      if x <. mk_isize 0 || (cast (x <: isize) <: u128) >. (cast (impl_8__MAX <: u32) <: u128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u32 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: isize) <: u32) <: t_Result u32 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_130: t_TryFrom u64 isize =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: isize) -> true);
    f_try_from_post
    =
    (fun (x: isize) (out: t_Result u64 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: isize) ->
      if x <. mk_isize 0 || (cast (x <: isize) <: u128) >. (cast (impl_9__MAX <: u64) <: u128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u64 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: isize) <: u64) <: t_Result u64 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_131: t_TryFrom u128 isize =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: isize) -> true);
    f_try_from_post
    =
    (fun (x: isize) (out: t_Result u128 Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: isize) ->
      if x <. mk_isize 0 || (cast (x <: isize) <: u128) >. impl_10__MAX
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result u128 Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: isize) <: u128)
        <:
        t_Result u128 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_132: t_TryFrom usize isize =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: isize) -> true);
    f_try_from_post
    =
    (fun (x: isize) (out: t_Result usize Core_models.Num.Error.t_TryFromIntError) -> true);
    f_try_from
    =
    fun (x: isize) ->
      if x <. mk_isize 0 || (cast (x <: isize) <: u128) >. (cast (impl_11__MAX <: usize) <: u128)
      then
        Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        t_Result usize Core_models.Num.Error.t_TryFromIntError
      else
        Result_Ok (cast (x <: isize) <: usize)
        <:
        t_Result usize Core_models.Num.Error.t_TryFromIntError
  }

let impl__new__from__chain
      (#v_A #v_B: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_A)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator v_B)
      (#_: unit{i1.f_Item == i0.f_Item})
      (a: v_A)
      (b: v_B)
    : t_Chain v_A v_B = { f_a = Option_Some a <: t_Option v_A; f_b = b } <: t_Chain v_A v_B

/// See [`std::iter::chain`]
let chain
      (#v_A #v_B: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_A)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator v_B)
      (#_: unit{i1.f_Item == i0.f_Item})
      (a: v_A)
      (b: v_B)
    : t_Chain v_A v_B = impl__new__from__chain #v_A #v_B a b

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1__from__chain':
    #v_A: Type0 ->
    #v_B: Type0 ->
    {| i0: t_Iterator v_A |} ->
    {| i1: t_Iterator v_B |} ->
    #_: unit{i1.f_Item == i0.f_Item}
  -> t_Iterator (t_Chain v_A v_B)

unfold
let impl_1__from__chain
      (#v_A #v_B: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_A)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator v_B)
      (#_: unit{i1.f_Item == i0.f_Item})
     = impl_1__from__chain' #v_A #v_B #i0 #i1 #_

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1__from__enumerate
      (#v_I: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
    : t_Iterator (t_Enumerate v_I) =
  {
    f_Item = (usize & i0.f_Item);
    f_next_pre = (fun (self: t_Enumerate v_I) -> true);
    f_next_post
    =
    (fun (self: t_Enumerate v_I) (out1: (t_Enumerate v_I & t_Option (usize & i0.f_Item))) -> true);
    f_next
    =
    fun (self: t_Enumerate v_I) ->
      let (tmp0: v_I), (out: t_Option i0.f_Item) =
        f_next #v_I #FStar.Tactics.Typeclasses.solve self.f_iter
      in
      let self:t_Enumerate v_I = { self with f_iter = tmp0 } <: t_Enumerate v_I in
      let (self: t_Enumerate v_I), (hax_temp_output: t_Option (usize & i0.f_Item)) =
        match out <: t_Option i0.f_Item with
        | Option_Some a ->
          let i:usize = self.f_count in
          let _:Prims.unit = Hax_lib.v_assume (b2t (self.f_count <. impl_11__MAX <: bool)) in
          let self:t_Enumerate v_I =
            { self with f_count = self.f_count +! mk_usize 1 } <: t_Enumerate v_I
          in
          self, (Option_Some (i, a <: (usize & i0.f_Item)) <: t_Option (usize & i0.f_Item))
          <:
          (t_Enumerate v_I & t_Option (usize & i0.f_Item))
        | Option_None  ->
          self, (Option_None <: t_Option (usize & i0.f_Item))
          <:
          (t_Enumerate v_I & t_Option (usize & i0.f_Item))
      in
      self, hax_temp_output <: (t_Enumerate v_I & t_Option (usize & i0.f_Item))
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1__from__filter':
    #v_I: Type0 ->
    #v_P: Type0 ->
    {| i0: t_Iterator v_I |} ->
    {| i1: Core_models.Ops.Function.t_Fn v_P i0.f_Item |}
  -> t_Iterator (t_Filter v_I v_P)

unfold
let impl_1__from__filter
      (#v_I #v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_P i0.f_Item)
     = impl_1__from__filter' #v_I #v_P #i0 #i1

let impl__new__from__flat_map
      (#v_I #v_U #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator v_U)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
      (it: v_I)
      (f: v_F)
    : t_FlatMap v_I v_U v_F =
  { f_it = it; f_f = f; f_current = Option_None <: t_Option v_U } <: t_FlatMap v_I v_U v_F

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1__from__flat_map':
    #v_I: Type0 ->
    #v_U: Type0 ->
    #v_F: Type0 ->
    {| i0: t_Iterator v_I |} ->
    {| i1: t_Iterator v_U |} ->
    {| i2: Core_models.Ops.Function.t_Fn v_F i0.f_Item |}
  -> t_Iterator (t_FlatMap v_I v_U v_F)

unfold
let impl_1__from__flat_map
      (#v_I #v_U #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator v_U)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
     = impl_1__from__flat_map' #v_I #v_U #v_F #i0 #i1 #i2

noeq

/// See [`std::iter::Flatten`]
type t_Flatten (v_I: Type0) {| i0: t_Iterator v_I |} {| i1: t_Iterator i0.f_Item |} = {
  f_it:v_I;
  f_current:t_Option i0.f_Item
}

let impl__new__from__flatten
      (#v_I: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator i0.f_Item)
      (it: v_I)
    : t_Flatten v_I = { f_it = it; f_current = Option_None <: t_Option i0.f_Item } <: t_Flatten v_I

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1__from__flatten':
    #v_I: Type0 ->
    {| i0: t_Iterator v_I |} ->
    {| i1: t_Iterator i0.f_Item |}
  -> t_Iterator (t_Flatten v_I)

unfold
let impl_1__from__flatten
      (#v_I: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator i0.f_Item)
     = impl_1__from__flatten' #v_I #i0 #i1

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1__from__map':
    #v_I: Type0 ->
    #v_O: Type0 ->
    #v_F: Type0 ->
    {| i0: t_Iterator v_I |} ->
    {| i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item |}
  -> t_Iterator (t_Map v_I v_F)

unfold
let impl_1__from__map
      (#v_I #v_O #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
     = impl_1__from__map' #v_I #v_O #v_F #i0 #i1

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1__from__skip': #v_I: Type0 -> {| i0: t_Iterator v_I |} -> t_Iterator (t_Skip v_I)

unfold
let impl_1__from__skip (#v_I: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I) =
  impl_1__from__skip' #v_I #i0

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1__from__step_by': #v_I: Type0 -> {| i0: t_Iterator v_I |} -> t_Iterator (t_StepBy v_I)

unfold
let impl_1__from__step_by
      (#v_I: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
     = impl_1__from__step_by' #v_I #i0

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1__from__take (#v_I: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
    : t_Iterator (t_Take v_I) =
  {
    f_Item = i0.f_Item;
    f_next_pre = (fun (self: t_Take v_I) -> true);
    f_next_post = (fun (self: t_Take v_I) (out1: (t_Take v_I & t_Option i0.f_Item)) -> true);
    f_next
    =
    fun (self: t_Take v_I) ->
      let (self: t_Take v_I), (hax_temp_output: t_Option i0.f_Item) =
        if self.f_n <>. mk_usize 0
        then
          let self:t_Take v_I = { self with f_n = self.f_n -! mk_usize 1 } <: t_Take v_I in
          let (tmp0: v_I), (out: t_Option i0.f_Item) =
            f_next #v_I #FStar.Tactics.Typeclasses.solve self.f_iter
          in
          let self:t_Take v_I = { self with f_iter = tmp0 } <: t_Take v_I in
          self, out <: (t_Take v_I & t_Option i0.f_Item)
        else self, (Option_None <: t_Option i0.f_Item) <: (t_Take v_I & t_Option i0.f_Item)
      in
      self, hax_temp_output <: (t_Take v_I & t_Option i0.f_Item)
  }

let impl__new__from__zip
      (#v_I1 #v_I2: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I1)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator v_I2)
      (it1: v_I1)
      (it2: v_I2)
    : t_Zip v_I1 v_I2 = { f_it1 = it1; f_it2 = it2 } <: t_Zip v_I1 v_I2

/// See [`std::iter::zip`]
let zip
      (#v_A #v_B: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_A)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator v_B)
      (a: v_A)
      (b: v_B)
    : t_Zip v_A v_B = impl__new__from__zip #v_A #v_B a b

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1__from__zip':
    #v_I1: Type0 ->
    #v_I2: Type0 ->
    {| i0: t_Iterator v_I1 |} ->
    {| i1: t_Iterator v_I2 |}
  -> t_Iterator (t_Zip v_I1 v_I2)

unfold
let impl_1__from__zip
      (#v_I1 #v_I2: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I1)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator v_I2)
     = impl_1__from__zip' #v_I1 #v_I2 #i0 #i1

assume
val iter_fold':
    #v_I: Type0 ->
    #v_B: Type0 ->
    #v_F: Type0 ->
    {| i0: t_Iterator v_I |} ->
    {| i1: Core_models.Ops.Function.t_Fn v_F (v_B & i0.f_Item) |} ->
    iter: v_I ->
    init: v_B ->
    f: v_F
  -> v_B

unfold
let iter_fold
      (#v_I #v_B #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Ops.Function.t_Fn v_F (v_B & i0.f_Item))
     = iter_fold' #v_I #v_B #v_F #i0 #i1

assume
val iter_all':
    #v_I: Type0 ->
    #v_F: Type0 ->
    {| i0: t_Iterator v_I |} ->
    {| i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item |} ->
    iter: v_I ->
    f: v_F
  -> bool

unfold
let iter_all
      (#v_I #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
     = iter_all' #v_I #v_F #i0 #i1

assume
val iter_any':
    #v_I: Type0 ->
    #v_F: Type0 ->
    {| i0: t_Iterator v_I |} ->
    {| i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item |} ->
    iter: v_I ->
    f: v_F
  -> bool

unfold
let iter_any
      (#v_I #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
     = iter_any' #v_I #v_F #i0 #i1

assume
val iter_find':
    #v_I: Type0 ->
    #v_P: Type0 ->
    {| i0: t_Iterator v_I |} ->
    {| i1: Core_models.Ops.Function.t_Fn v_P i0.f_Item |} ->
    iter: v_I ->
    predicate: v_P
  -> (v_I & t_Option i0.f_Item)

unfold
let iter_find
      (#v_I #v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_P i0.f_Item)
     = iter_find' #v_I #v_P #i0 #i1

assume
val iter_find_map':
    #v_I: Type0 ->
    #v_B: Type0 ->
    #v_F: Type0 ->
    {| i0: t_Iterator v_I |} ->
    {| i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item |} ->
    iter: v_I ->
    f: v_F
  -> t_Option v_B

unfold
let iter_find_map
      (#v_I #v_B #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
     = iter_find_map' #v_I #v_B #v_F #i0 #i1

assume
val iter_position':
    #v_I: Type0 ->
    #v_P: Type0 ->
    {| i0: t_Iterator v_I |} ->
    {| i1: Core_models.Ops.Function.t_Fn v_P i0.f_Item |} ->
    iter: v_I ->
    predicate: v_P
  -> t_Option usize

unfold
let iter_position
      (#v_I #v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_P i0.f_Item)
     = iter_position' #v_I #v_P #i0 #i1

assume
val iter_count': #v_I: Type0 -> {| i0: t_Iterator v_I |} -> iter: v_I -> usize

unfold
let iter_count (#v_I: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I) =
  iter_count' #v_I #i0

assume
val iter_nth': #v_I: Type0 -> {| i0: t_Iterator v_I |} -> iter: v_I -> n: usize
  -> t_Option i0.f_Item

unfold
let iter_nth (#v_I: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I) =
  iter_nth' #v_I #i0

assume
val iter_last': #v_I: Type0 -> {| i0: t_Iterator v_I |} -> iter: v_I -> t_Option i0.f_Item

unfold
let iter_last (#v_I: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I) =
  iter_last' #v_I #i0

assume
val iter_for_each':
    #v_I: Type0 ->
    #v_F: Type0 ->
    {| i0: t_Iterator v_I |} ->
    {| i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item |} ->
    iter: v_I ->
    f: v_F
  -> Prims.unit

unfold
let iter_for_each
      (#v_I #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
     = iter_for_each' #v_I #v_F #i0 #i1

assume
val iter_reduce':
    #v_I: Type0 ->
    #v_F: Type0 ->
    {| i0: t_Iterator v_I |} ->
    {| i1: Core_models.Ops.Function.t_Fn v_F (i0.f_Item & i0.f_Item) |} ->
    iter: v_I ->
    f: v_F
  -> t_Option i0.f_Item

unfold
let iter_reduce
      (#v_I #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Ops.Function.t_Fn v_F (i0.f_Item & i0.f_Item))
     = iter_reduce' #v_I #v_F #i0 #i1

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1 (#v_I: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
    : Core_models.Iter.Traits.Collect.t_IntoIterator v_I =
  {
    f_Item = i0.f_Item;
    f_IntoIter = v_I;
    f_into_iter_pre = (fun (self: v_I) -> true);
    f_into_iter_post = (fun (self: v_I) (out: v_I) -> true);
    f_into_iter = fun (self: v_I) -> self
  }

let is_lt
      (#v_T #v_U: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_PartialOrd v_T v_U)
      (a: v_T)
      (b: v_U)
    : bool =
  match f_partial_cmp #v_T #v_U #FStar.Tactics.Typeclasses.solve a b <: t_Option t_Ordering with
  | Option_Some (Ordering_Less ) -> true
  | _ -> false

let is_le
      (#v_T #v_U: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_PartialOrd v_T v_U)
      (a: v_T)
      (b: v_U)
    : bool =
  match f_partial_cmp #v_T #v_U #FStar.Tactics.Typeclasses.solve a b <: t_Option t_Ordering with
  | Option_Some (Ordering_Less ) | Option_Some (Ordering_Equal ) -> true
  | _ -> false

let bounds_contain
      (#v_T #v_U: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_PartialOrd v_T v_U)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_PartialOrd v_U v_T)
      (start v_end: t_Bound v_T)
      (item: v_U)
    : bool =
  let above_start:bool =
    match start <: t_Bound v_T with
    | Bound_Included s -> is_le #v_T #v_U s item
    | Bound_Excluded s -> is_lt #v_T #v_U s item
    | Bound_Unbounded  -> true
  in
  let below_end:bool =
    match v_end <: t_Bound v_T with
    | Bound_Included e -> is_le #v_U #v_T item e
    | Bound_Excluded e -> is_lt #v_U #v_T item e
    | Bound_Unbounded  -> true
  in
  above_start && below_end

let bounds_are_empty
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_PartialOrd v_T v_T)
      (start v_end: t_Bound v_T)
    : bool =
  let non_empty:bool =
    match start, v_end <: (t_Bound v_T & t_Bound v_T) with
    | Bound_Unbounded , _ -> true
    | _, Bound_Unbounded  -> true
    | Bound_Included s, Bound_Included e -> is_le #v_T #v_T s e
    | Bound_Included s, Bound_Excluded e -> is_lt #v_T #v_T s e
    | Bound_Excluded s, Bound_Included e -> is_lt #v_T #v_T s e
    | Bound_Excluded s, Bound_Excluded e -> is_lt #v_T #v_T s e
  in
  non_empty =. false

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_11__from__range (#v_T: Type0) : t_IntoBounds (t_Range v_T) v_T =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_into_bounds_pre = (fun (self: t_Range v_T) -> true);
    f_into_bounds_post = (fun (self: t_Range v_T) (out: (t_Bound v_T & t_Bound v_T)) -> true);
    f_into_bounds
    =
    fun (self: t_Range v_T) ->
      (Bound_Included self.f_start <: t_Bound v_T), (Bound_Excluded self.f_end <: t_Bound v_T)
      <:
      (t_Bound v_T & t_Bound v_T)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_12__from__range (#v_T: Type0) : t_IntoBounds (t_RangeFrom v_T) v_T =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_into_bounds_pre = (fun (self: t_RangeFrom v_T) -> true);
    f_into_bounds_post = (fun (self: t_RangeFrom v_T) (out: (t_Bound v_T & t_Bound v_T)) -> true);
    f_into_bounds
    =
    fun (self: t_RangeFrom v_T) ->
      (Bound_Included self.f_start <: t_Bound v_T), (Bound_Unbounded <: t_Bound v_T)
      <:
      (t_Bound v_T & t_Bound v_T)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_13__from__range (#v_T: Type0) : t_IntoBounds (t_RangeTo v_T) v_T =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_into_bounds_pre = (fun (self: t_RangeTo v_T) -> true);
    f_into_bounds_post = (fun (self: t_RangeTo v_T) (out: (t_Bound v_T & t_Bound v_T)) -> true);
    f_into_bounds
    =
    fun (self: t_RangeTo v_T) ->
      (Bound_Unbounded <: t_Bound v_T), (Bound_Excluded self.f_end <: t_Bound v_T)
      <:
      (t_Bound v_T & t_Bound v_T)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_14__from__range (#v_T: Type0) : t_IntoBounds t_RangeFull v_T =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_into_bounds_pre = (fun (self: t_RangeFull) -> true);
    f_into_bounds_post = (fun (self: t_RangeFull) (out: (t_Bound v_T & t_Bound v_T)) -> true);
    f_into_bounds
    =
    fun (self: t_RangeFull) ->
      (Bound_Unbounded <: t_Bound v_T), (Bound_Unbounded <: t_Bound v_T)
      <:
      (t_Bound v_T & t_Bound v_T)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_15__from__range (#v_T: Type0) : t_IntoBounds (t_RangeInclusive v_T) v_T =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_into_bounds_pre = (fun (self: t_RangeInclusive v_T) -> true);
    f_into_bounds_post
    =
    (fun (self: t_RangeInclusive v_T) (out: (t_Bound v_T & t_Bound v_T)) -> true);
    f_into_bounds
    =
    fun (self: t_RangeInclusive v_T) ->
      (Bound_Included self.f_start <: t_Bound v_T), (Bound_Included self.f_end <: t_Bound v_T)
      <:
      (t_Bound v_T & t_Bound v_T)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_16__from__range (#v_T: Type0) : t_IntoBounds (t_RangeToInclusive v_T) v_T =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_into_bounds_pre = (fun (self: t_RangeToInclusive v_T) -> true);
    f_into_bounds_post
    =
    (fun (self: t_RangeToInclusive v_T) (out: (t_Bound v_T & t_Bound v_T)) -> true);
    f_into_bounds
    =
    fun (self: t_RangeToInclusive v_T) ->
      (Bound_Unbounded <: t_Bound v_T), (Bound_Included self.f_end <: t_Bound v_T)
      <:
      (t_Bound v_T & t_Bound v_T)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_17__from__range (#v_T: Type0) : t_OneSidedRange (t_RangeFrom v_T) v_T =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_bound_pre = (fun (self: t_RangeFrom v_T) -> true);
    f_bound_post = (fun (self: t_RangeFrom v_T) (out: (t_OneSidedRangeBound & v_T)) -> true);
    f_bound
    =
    fun (self: t_RangeFrom v_T) ->
      (OneSidedRangeBound_StartInclusive <: t_OneSidedRangeBound), self.f_start
      <:
      (t_OneSidedRangeBound & v_T)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_18__from__range (#v_T: Type0) : t_OneSidedRange (t_RangeTo v_T) v_T =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_bound_pre = (fun (self: t_RangeTo v_T) -> true);
    f_bound_post = (fun (self: t_RangeTo v_T) (out: (t_OneSidedRangeBound & v_T)) -> true);
    f_bound
    =
    fun (self: t_RangeTo v_T) ->
      (OneSidedRangeBound_End <: t_OneSidedRangeBound), self.f_end <: (t_OneSidedRangeBound & v_T)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_19__from__range (#v_T: Type0) : t_OneSidedRange (t_RangeToInclusive v_T) v_T =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_bound_pre = (fun (self: t_RangeToInclusive v_T) -> true);
    f_bound_post = (fun (self: t_RangeToInclusive v_T) (out: (t_OneSidedRangeBound & v_T)) -> true);
    f_bound
    =
    fun (self: t_RangeToInclusive v_T) ->
      (OneSidedRangeBound_EndInclusive <: t_OneSidedRangeBound), self.f_end
      <:
      (t_OneSidedRangeBound & v_T)
  }

/// See [`std::ops::Range::contains`]
let impl_20__contains
      (#v_Idx #v_U: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_PartialOrd v_Idx v_Idx)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_PartialOrd v_Idx v_U)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: t_PartialOrd v_U v_Idx)
      (self: t_Range v_Idx)
      (item: v_U)
    : bool =
  bounds_contain #v_Idx
    #v_U
    (f_start_bound #(t_Range v_Idx) #v_Idx #FStar.Tactics.Typeclasses.solve self <: t_Bound v_Idx)
    (f_end_bound #(t_Range v_Idx) #v_Idx #FStar.Tactics.Typeclasses.solve self <: t_Bound v_Idx)
    item

/// See [`std::ops::Range::is_empty`]
let impl_20__is_empty
      (#v_Idx: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_PartialOrd v_Idx v_Idx)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_PartialOrd v_Idx v_Idx)
      (self: t_Range v_Idx)
    : bool = (is_lt #v_Idx #v_Idx self.f_start self.f_end <: bool) =. false

/// See [`std::ops::RangeFrom::contains`]
let impl_21__contains
      (#v_Idx #v_U: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_PartialOrd v_Idx v_Idx)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_PartialOrd v_Idx v_U)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: t_PartialOrd v_U v_Idx)
      (self: t_RangeFrom v_Idx)
      (item: v_U)
    : bool =
  bounds_contain #v_Idx
    #v_U
    (f_start_bound #(t_RangeFrom v_Idx) #v_Idx #FStar.Tactics.Typeclasses.solve self
      <:
      t_Bound v_Idx)
    (f_end_bound #(t_RangeFrom v_Idx) #v_Idx #FStar.Tactics.Typeclasses.solve self <: t_Bound v_Idx)
    item

/// See [`std::ops::RangeTo::contains`]
let impl_22__contains
      (#v_Idx #v_U: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_PartialOrd v_Idx v_Idx)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_PartialOrd v_Idx v_U)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: t_PartialOrd v_U v_Idx)
      (self: t_RangeTo v_Idx)
      (item: v_U)
    : bool =
  bounds_contain #v_Idx
    #v_U
    (f_start_bound #(t_RangeTo v_Idx) #v_Idx #FStar.Tactics.Typeclasses.solve self <: t_Bound v_Idx)
    (f_end_bound #(t_RangeTo v_Idx) #v_Idx #FStar.Tactics.Typeclasses.solve self <: t_Bound v_Idx)
    item

/// See [`std::ops::RangeToInclusive::contains`]
let impl_23__contains
      (#v_Idx #v_U: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_PartialOrd v_Idx v_Idx)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_PartialOrd v_Idx v_U)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: t_PartialOrd v_U v_Idx)
      (self: t_RangeToInclusive v_Idx)
      (item: v_U)
    : bool =
  bounds_contain #v_Idx
    #v_U
    (f_start_bound #(t_RangeToInclusive v_Idx) #v_Idx #FStar.Tactics.Typeclasses.solve self
      <:
      t_Bound v_Idx)
    (f_end_bound #(t_RangeToInclusive v_Idx) #v_Idx #FStar.Tactics.Typeclasses.solve self
      <:
      t_Bound v_Idx)
    item

/// See [`std::ops::RangeInclusive::contains`]
let impl_26__contains
      (#v_Idx #v_U: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_PartialOrd v_Idx v_Idx)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_PartialOrd v_Idx v_U)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: t_PartialOrd v_U v_Idx)
      (self: t_RangeInclusive v_Idx)
      (item: v_U)
    : bool =
  bounds_contain #v_Idx
    #v_U
    (f_start_bound #(t_RangeInclusive v_Idx) #v_Idx #FStar.Tactics.Typeclasses.solve self
      <:
      t_Bound v_Idx)
    (f_end_bound #(t_RangeInclusive v_Idx) #v_Idx #FStar.Tactics.Typeclasses.solve self
      <:
      t_Bound v_Idx)
    item

/// See [`std::ops::RangeInclusive::is_empty`]
let impl_26__is_empty
      (#v_Idx: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_PartialOrd v_Idx v_Idx)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_PartialOrd v_Idx v_Idx)
      (self: t_RangeInclusive v_Idx)
    : bool = (is_le #v_Idx #v_Idx self.f_start self.f_end <: bool) =. false

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_27__from__range: t_Iterator (t_Range u8) =
  {
    f_Item = u8;
    f_next_pre = (fun (self: t_Range u8) -> true);
    f_next_post = (fun (self: t_Range u8) (out: (t_Range u8 & t_Option u8)) -> true);
    f_next
    =
    fun (self: t_Range u8) ->
      let (self: t_Range u8), (hax_temp_output: t_Option u8) =
        if self.f_start >=. self.f_end
        then self, (Option_None <: t_Option u8) <: (t_Range u8 & t_Option u8)
        else
          let res:u8 = self.f_start in
          let self:t_Range u8 = { self with f_start = self.f_start +! mk_u8 1 } <: t_Range u8 in
          self, (Option_Some res <: t_Option u8) <: (t_Range u8 & t_Option u8)
      in
      self, hax_temp_output <: (t_Range u8 & t_Option u8)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_28__from__range: t_Iterator (t_Range u16) =
  {
    f_Item = u16;
    f_next_pre = (fun (self: t_Range u16) -> true);
    f_next_post = (fun (self: t_Range u16) (out: (t_Range u16 & t_Option u16)) -> true);
    f_next
    =
    fun (self: t_Range u16) ->
      let (self: t_Range u16), (hax_temp_output: t_Option u16) =
        if self.f_start >=. self.f_end
        then self, (Option_None <: t_Option u16) <: (t_Range u16 & t_Option u16)
        else
          let res:u16 = self.f_start in
          let self:t_Range u16 = { self with f_start = self.f_start +! mk_u16 1 } <: t_Range u16 in
          self, (Option_Some res <: t_Option u16) <: (t_Range u16 & t_Option u16)
      in
      self, hax_temp_output <: (t_Range u16 & t_Option u16)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_29__from__range: t_Iterator (t_Range u32) =
  {
    f_Item = u32;
    f_next_pre = (fun (self: t_Range u32) -> true);
    f_next_post = (fun (self: t_Range u32) (out: (t_Range u32 & t_Option u32)) -> true);
    f_next
    =
    fun (self: t_Range u32) ->
      let (self: t_Range u32), (hax_temp_output: t_Option u32) =
        if self.f_start >=. self.f_end
        then self, (Option_None <: t_Option u32) <: (t_Range u32 & t_Option u32)
        else
          let res:u32 = self.f_start in
          let self:t_Range u32 = { self with f_start = self.f_start +! mk_u32 1 } <: t_Range u32 in
          self, (Option_Some res <: t_Option u32) <: (t_Range u32 & t_Option u32)
      in
      self, hax_temp_output <: (t_Range u32 & t_Option u32)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_30__from__range: t_Iterator (t_Range u64) =
  {
    f_Item = u64;
    f_next_pre = (fun (self: t_Range u64) -> true);
    f_next_post = (fun (self: t_Range u64) (out: (t_Range u64 & t_Option u64)) -> true);
    f_next
    =
    fun (self: t_Range u64) ->
      let (self: t_Range u64), (hax_temp_output: t_Option u64) =
        if self.f_start >=. self.f_end
        then self, (Option_None <: t_Option u64) <: (t_Range u64 & t_Option u64)
        else
          let res:u64 = self.f_start in
          let self:t_Range u64 = { self with f_start = self.f_start +! mk_u64 1 } <: t_Range u64 in
          self, (Option_Some res <: t_Option u64) <: (t_Range u64 & t_Option u64)
      in
      self, hax_temp_output <: (t_Range u64 & t_Option u64)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_31__from__range: t_Iterator (t_Range u128) =
  {
    f_Item = u128;
    f_next_pre = (fun (self: t_Range u128) -> true);
    f_next_post = (fun (self: t_Range u128) (out: (t_Range u128 & t_Option u128)) -> true);
    f_next
    =
    fun (self: t_Range u128) ->
      let (self: t_Range u128), (hax_temp_output: t_Option u128) =
        if self.f_start >=. self.f_end
        then self, (Option_None <: t_Option u128) <: (t_Range u128 & t_Option u128)
        else
          let res:u128 = self.f_start in
          let self:t_Range u128 =
            { self with f_start = self.f_start +! mk_u128 1 } <: t_Range u128
          in
          self, (Option_Some res <: t_Option u128) <: (t_Range u128 & t_Option u128)
      in
      self, hax_temp_output <: (t_Range u128 & t_Option u128)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_32__from__range: t_Iterator (t_Range usize) =
  {
    f_Item = usize;
    f_next_pre = (fun (self: t_Range usize) -> true);
    f_next_post = (fun (self: t_Range usize) (out: (t_Range usize & t_Option usize)) -> true);
    f_next
    =
    fun (self: t_Range usize) ->
      let (self: t_Range usize), (hax_temp_output: t_Option usize) =
        if self.f_start >=. self.f_end
        then self, (Option_None <: t_Option usize) <: (t_Range usize & t_Option usize)
        else
          let res:usize = self.f_start in
          let self:t_Range usize =
            { self with f_start = self.f_start +! mk_usize 1 } <: t_Range usize
          in
          self, (Option_Some res <: t_Option usize) <: (t_Range usize & t_Option usize)
      in
      self, hax_temp_output <: (t_Range usize & t_Option usize)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_33__from__range: t_Iterator (t_Range i8) =
  {
    f_Item = i8;
    f_next_pre = (fun (self: t_Range i8) -> true);
    f_next_post = (fun (self: t_Range i8) (out: (t_Range i8 & t_Option i8)) -> true);
    f_next
    =
    fun (self: t_Range i8) ->
      let (self: t_Range i8), (hax_temp_output: t_Option i8) =
        if self.f_start >=. self.f_end
        then self, (Option_None <: t_Option i8) <: (t_Range i8 & t_Option i8)
        else
          let res:i8 = self.f_start in
          let self:t_Range i8 = { self with f_start = self.f_start +! mk_i8 1 } <: t_Range i8 in
          self, (Option_Some res <: t_Option i8) <: (t_Range i8 & t_Option i8)
      in
      self, hax_temp_output <: (t_Range i8 & t_Option i8)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_34__from__range: t_Iterator (t_Range i16) =
  {
    f_Item = i16;
    f_next_pre = (fun (self: t_Range i16) -> true);
    f_next_post = (fun (self: t_Range i16) (out: (t_Range i16 & t_Option i16)) -> true);
    f_next
    =
    fun (self: t_Range i16) ->
      let (self: t_Range i16), (hax_temp_output: t_Option i16) =
        if self.f_start >=. self.f_end
        then self, (Option_None <: t_Option i16) <: (t_Range i16 & t_Option i16)
        else
          let res:i16 = self.f_start in
          let self:t_Range i16 = { self with f_start = self.f_start +! mk_i16 1 } <: t_Range i16 in
          self, (Option_Some res <: t_Option i16) <: (t_Range i16 & t_Option i16)
      in
      self, hax_temp_output <: (t_Range i16 & t_Option i16)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_35__from__range: t_Iterator (t_Range i32) =
  {
    f_Item = i32;
    f_next_pre = (fun (self: t_Range i32) -> true);
    f_next_post = (fun (self: t_Range i32) (out: (t_Range i32 & t_Option i32)) -> true);
    f_next
    =
    fun (self: t_Range i32) ->
      let (self: t_Range i32), (hax_temp_output: t_Option i32) =
        if self.f_start >=. self.f_end
        then self, (Option_None <: t_Option i32) <: (t_Range i32 & t_Option i32)
        else
          let res:i32 = self.f_start in
          let self:t_Range i32 = { self with f_start = self.f_start +! mk_i32 1 } <: t_Range i32 in
          self, (Option_Some res <: t_Option i32) <: (t_Range i32 & t_Option i32)
      in
      self, hax_temp_output <: (t_Range i32 & t_Option i32)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_36__from__range: t_Iterator (t_Range i64) =
  {
    f_Item = i64;
    f_next_pre = (fun (self: t_Range i64) -> true);
    f_next_post = (fun (self: t_Range i64) (out: (t_Range i64 & t_Option i64)) -> true);
    f_next
    =
    fun (self: t_Range i64) ->
      let (self: t_Range i64), (hax_temp_output: t_Option i64) =
        if self.f_start >=. self.f_end
        then self, (Option_None <: t_Option i64) <: (t_Range i64 & t_Option i64)
        else
          let res:i64 = self.f_start in
          let self:t_Range i64 = { self with f_start = self.f_start +! mk_i64 1 } <: t_Range i64 in
          self, (Option_Some res <: t_Option i64) <: (t_Range i64 & t_Option i64)
      in
      self, hax_temp_output <: (t_Range i64 & t_Option i64)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_37__from__range: t_Iterator (t_Range i128) =
  {
    f_Item = i128;
    f_next_pre = (fun (self: t_Range i128) -> true);
    f_next_post = (fun (self: t_Range i128) (out: (t_Range i128 & t_Option i128)) -> true);
    f_next
    =
    fun (self: t_Range i128) ->
      let (self: t_Range i128), (hax_temp_output: t_Option i128) =
        if self.f_start >=. self.f_end
        then self, (Option_None <: t_Option i128) <: (t_Range i128 & t_Option i128)
        else
          let res:i128 = self.f_start in
          let self:t_Range i128 =
            { self with f_start = self.f_start +! mk_i128 1 } <: t_Range i128
          in
          self, (Option_Some res <: t_Option i128) <: (t_Range i128 & t_Option i128)
      in
      self, hax_temp_output <: (t_Range i128 & t_Option i128)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_38__from__range: t_Iterator (t_Range isize) =
  {
    f_Item = isize;
    f_next_pre = (fun (self: t_Range isize) -> true);
    f_next_post = (fun (self: t_Range isize) (out: (t_Range isize & t_Option isize)) -> true);
    f_next
    =
    fun (self: t_Range isize) ->
      let (self: t_Range isize), (hax_temp_output: t_Option isize) =
        if self.f_start >=. self.f_end
        then self, (Option_None <: t_Option isize) <: (t_Range isize & t_Option isize)
        else
          let res:isize = self.f_start in
          let self:t_Range isize =
            { self with f_start = self.f_start +! mk_isize 1 } <: t_Range isize
          in
          self, (Option_Some res <: t_Option isize) <: (t_Range isize & t_Option isize)
      in
      self, hax_temp_output <: (t_Range isize & t_Option isize)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_14__from__option (#v_T: Type0) : t_Iterator (t_Iter v_T) =
  {
    f_Item = v_T;
    f_next_pre = (fun (self: t_Iter v_T) -> true);
    f_next_post = (fun (self: t_Iter v_T) (out1: (t_Iter v_T & t_Option v_T)) -> true);
    f_next
    =
    fun (self: t_Iter v_T) ->
      let (self: t_Iter v_T), (hax_temp_output: t_Option v_T) =
        if (Rust_primitives.Sequence.seq_len #v_T self._0 <: usize) =. mk_usize 0
        then self, (Option_None <: t_Option v_T) <: (t_Iter v_T & t_Option v_T)
        else
          let (tmp0: Rust_primitives.Sequence.t_Seq v_T), (out: v_T) =
            Rust_primitives.Sequence.seq_remove #v_T self._0 (mk_usize 0)
          in
          let self:t_Iter v_T = { self with _0 = tmp0 } <: t_Iter v_T in
          self, (Option_Some out <: t_Option v_T) <: (t_Iter v_T & t_Option v_T)
      in
      self, hax_temp_output <: (t_Iter v_T & t_Option v_T)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_16__from__option (#v_T: Type0) : t_Iterator (t_IntoIter__from__option v_T) =
  {
    f_Item = v_T;
    f_next_pre = (fun (self: t_IntoIter__from__option v_T) -> true);
    f_next_post
    =
    (fun
        (self: t_IntoIter__from__option v_T)
        (out1: (t_IntoIter__from__option v_T & t_Option v_T))
        ->
        true);
    f_next
    =
    fun (self: t_IntoIter__from__option v_T) ->
      let (self: t_IntoIter__from__option v_T), (hax_temp_output: t_Option v_T) =
        if (Rust_primitives.Sequence.seq_len #v_T self._0 <: usize) =. mk_usize 0
        then self, (Option_None <: t_Option v_T) <: (t_IntoIter__from__option v_T & t_Option v_T)
        else
          let (tmp0: Rust_primitives.Sequence.t_Seq v_T), (out: v_T) =
            Rust_primitives.Sequence.seq_remove #v_T self._0 (mk_usize 0)
          in
          let self:t_IntoIter__from__option v_T =
            { self with _0 = tmp0 } <: t_IntoIter__from__option v_T
          in
          self, (Option_Some out <: t_Option v_T) <: (t_IntoIter__from__option v_T & t_Option v_T)
      in
      self, hax_temp_output <: (t_IntoIter__from__option v_T & t_Option v_T)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_18__from__option': #v_A: Type0 -> {| i0: t_Iterator v_A |}
  -> t_Iterator (t_OptionFlatten v_A)

unfold
let impl_18__from__option
      (#v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_A)
     = impl_18__from__option' #v_A #i0

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7__from__result (#v_T: Type0) : t_Iterator (t_Iter__from__result v_T) =
  {
    f_Item = v_T;
    f_next_pre = (fun (self: t_Iter__from__result v_T) -> true);
    f_next_post
    =
    (fun (self: t_Iter__from__result v_T) (out1: (t_Iter__from__result v_T & t_Option v_T)) -> true);
    f_next
    =
    fun (self: t_Iter__from__result v_T) ->
      let (self: t_Iter__from__result v_T), (hax_temp_output: t_Option v_T) =
        if (Rust_primitives.Sequence.seq_len #v_T self._0 <: usize) =. mk_usize 0
        then self, (Option_None <: t_Option v_T) <: (t_Iter__from__result v_T & t_Option v_T)
        else
          let (tmp0: Rust_primitives.Sequence.t_Seq v_T), (out: v_T) =
            Rust_primitives.Sequence.seq_remove #v_T self._0 (mk_usize 0)
          in
          let self:t_Iter__from__result v_T = { self with _0 = tmp0 } <: t_Iter__from__result v_T in
          self, (Option_Some out <: t_Option v_T) <: (t_Iter__from__result v_T & t_Option v_T)
      in
      self, hax_temp_output <: (t_Iter__from__result v_T & t_Option v_T)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9__from__result (#v_T: Type0) : t_Iterator (t_IntoIter__from__result v_T) =
  {
    f_Item = v_T;
    f_next_pre = (fun (self: t_IntoIter__from__result v_T) -> true);
    f_next_post
    =
    (fun
        (self: t_IntoIter__from__result v_T)
        (out1: (t_IntoIter__from__result v_T & t_Option v_T))
        ->
        true);
    f_next
    =
    fun (self: t_IntoIter__from__result v_T) ->
      let (self: t_IntoIter__from__result v_T), (hax_temp_output: t_Option v_T) =
        if (Rust_primitives.Sequence.seq_len #v_T self._0 <: usize) =. mk_usize 0
        then self, (Option_None <: t_Option v_T) <: (t_IntoIter__from__result v_T & t_Option v_T)
        else
          let (tmp0: Rust_primitives.Sequence.t_Seq v_T), (out: v_T) =
            Rust_primitives.Sequence.seq_remove #v_T self._0 (mk_usize 0)
          in
          let self:t_IntoIter__from__result v_T =
            { self with _0 = tmp0 } <: t_IntoIter__from__result v_T
          in
          self, (Option_Some out <: t_Option v_T) <: (t_IntoIter__from__result v_T & t_Option v_T)
      in
      self, hax_temp_output <: (t_IntoIter__from__result v_T & t_Option v_T)
  }

/// See [`std::cmp::Ord`]
class t_Ord (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:t_Eq v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i1:t_PartialOrd v_Self v_Self;
  f_cmp_pre:self_: v_Self -> other: v_Self -> pred: Type0{true ==> pred};
  f_cmp_post:v_Self -> v_Self -> t_Ordering -> Type0;
  f_cmp:x0: v_Self -> x1: v_Self
    -> Prims.Pure t_Ordering (f_cmp_pre x0 x1) (fun result -> f_cmp_post x0 x1 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_Ord v_Self|} -> i._super_i0

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_Ord v_Self|} -> i._super_i1

class t_PartialOrdDefaults (v_Self: Type0) (v_Rhs: Type0) = {
  f_lt_pre:{| i1: t_PartialOrd v_Self v_Rhs |} -> self_: v_Self -> y: v_Rhs
    -> pred: Type0{true ==> pred};
  f_lt_post:{| i1: t_PartialOrd v_Self v_Rhs |} -> v_Self -> v_Rhs -> bool -> Type0;
  f_lt:{| i1: t_PartialOrd v_Self v_Rhs |} -> x0: v_Self -> x1: v_Rhs
    -> Prims.Pure bool (f_lt_pre #i1 x0 x1) (fun result -> f_lt_post #i1 x0 x1 result);
  f_le_pre:{| i1: t_PartialOrd v_Self v_Rhs |} -> self_: v_Self -> y: v_Rhs
    -> pred: Type0{true ==> pred};
  f_le_post:{| i1: t_PartialOrd v_Self v_Rhs |} -> v_Self -> v_Rhs -> bool -> Type0;
  f_le:{| i1: t_PartialOrd v_Self v_Rhs |} -> x0: v_Self -> x1: v_Rhs
    -> Prims.Pure bool (f_le_pre #i1 x0 x1) (fun result -> f_le_post #i1 x0 x1 result);
  f_gt_pre:{| i1: t_PartialOrd v_Self v_Rhs |} -> self_: v_Self -> y: v_Rhs
    -> pred: Type0{true ==> pred};
  f_gt_post:{| i1: t_PartialOrd v_Self v_Rhs |} -> v_Self -> v_Rhs -> bool -> Type0;
  f_gt:{| i1: t_PartialOrd v_Self v_Rhs |} -> x0: v_Self -> x1: v_Rhs
    -> Prims.Pure bool (f_gt_pre #i1 x0 x1) (fun result -> f_gt_post #i1 x0 x1 result);
  f_ge_pre:{| i1: t_PartialOrd v_Self v_Rhs |} -> self_: v_Self -> y: v_Rhs
    -> pred: Type0{true ==> pred};
  f_ge_post:{| i1: t_PartialOrd v_Self v_Rhs |} -> v_Self -> v_Rhs -> bool -> Type0;
  f_ge:{| i1: t_PartialOrd v_Self v_Rhs |} -> x0: v_Self -> x1: v_Rhs
    -> Prims.Pure bool (f_ge_pre #i1 x0 x1) (fun result -> f_ge_post #i1 x0 x1 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1__from__cmp
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_PartialOrd v_T v_T)
    : t_PartialOrdDefaults v_T v_T =
  {
    f_lt_pre
    =
    (fun
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_PartialOrd v_T v_T)
        (self: v_T)
        (y: v_T)
        ->
        true);
    f_lt_post
    =
    (fun
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_PartialOrd v_T v_T)
        (self: v_T)
        (y: v_T)
        (out: bool)
        ->
        true);
    f_lt
    =
    (fun
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_PartialOrd v_T v_T)
        (self: v_T)
        (y: v_T)
        ->
        match
          f_partial_cmp #v_T #v_T #FStar.Tactics.Typeclasses.solve self y <: t_Option t_Ordering
        with
        | Option_Some (Ordering_Less ) -> true
        | _ -> false);
    f_le_pre
    =
    (fun
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_PartialOrd v_T v_T)
        (self: v_T)
        (y: v_T)
        ->
        true);
    f_le_post
    =
    (fun
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_PartialOrd v_T v_T)
        (self: v_T)
        (y: v_T)
        (out: bool)
        ->
        true);
    f_le
    =
    (fun
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_PartialOrd v_T v_T)
        (self: v_T)
        (y: v_T)
        ->
        match
          f_partial_cmp #v_T #v_T #FStar.Tactics.Typeclasses.solve self y <: t_Option t_Ordering
        with
        | Option_Some (Ordering_Less ) | Option_Some (Ordering_Equal ) -> true
        | _ -> false);
    f_gt_pre
    =
    (fun
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_PartialOrd v_T v_T)
        (self: v_T)
        (y: v_T)
        ->
        true);
    f_gt_post
    =
    (fun
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_PartialOrd v_T v_T)
        (self: v_T)
        (y: v_T)
        (out: bool)
        ->
        true);
    f_gt
    =
    (fun
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_PartialOrd v_T v_T)
        (self: v_T)
        (y: v_T)
        ->
        match
          f_partial_cmp #v_T #v_T #FStar.Tactics.Typeclasses.solve self y <: t_Option t_Ordering
        with
        | Option_Some (Ordering_Greater ) -> true
        | _ -> false);
    f_ge_pre
    =
    (fun
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_PartialOrd v_T v_T)
        (self: v_T)
        (y: v_T)
        ->
        true);
    f_ge_post
    =
    (fun
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_PartialOrd v_T v_T)
        (self: v_T)
        (y: v_T)
        (out: bool)
        ->
        true);
    f_ge
    =
    fun (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_PartialOrd v_T v_T) (self: v_T) (y: v_T) ->
      match
        f_partial_cmp #v_T #v_T #FStar.Tactics.Typeclasses.solve self y <: t_Option t_Ordering
      with
      | Option_Some (Ordering_Greater ) | Option_Some (Ordering_Equal ) -> true
      | _ -> false
  }

/// See [`std::cmp::max`]
let max (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Ord v_T) (v1 v2: v_T) : v_T =
  match f_cmp #v_T #FStar.Tactics.Typeclasses.solve v1 v2 <: t_Ordering with
  | Ordering_Greater  -> v1
  | _ -> v2

/// See [`std::cmp::min`]
let min (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Ord v_T) (v1 v2: v_T) : v_T =
  match f_cmp #v_T #FStar.Tactics.Typeclasses.solve v1 v2 <: t_Ordering with
  | Ordering_Greater  -> v2
  | _ -> v1

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5__from__cmp (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Ord v_T)
    : t_Ord (t_Reverse v_T) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    _super_i1 = FStar.Tactics.Typeclasses.solve;
    f_cmp_pre = (fun (self: t_Reverse v_T) (other: t_Reverse v_T) -> true);
    f_cmp_post = (fun (self: t_Reverse v_T) (other: t_Reverse v_T) (out: t_Ordering) -> true);
    f_cmp
    =
    fun (self: t_Reverse v_T) (other: t_Reverse v_T) ->
      f_cmp #v_T #FStar.Tactics.Typeclasses.solve other._0 self._0
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_31__from__cmp: t_Ord u8 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    _super_i1 = FStar.Tactics.Typeclasses.solve;
    f_cmp_pre = (fun (self: u8) (other: u8) -> true);
    f_cmp_post
    =
    (fun (self_: u8) (other: u8) (res: t_Ordering) ->
        match res <: t_Ordering with
        | Ordering_Less  -> self_ <. other
        | Ordering_Equal  -> self_ =. other
        | Ordering_Greater  -> self_ >. other);
    f_cmp
    =
    fun (self: u8) (other: u8) ->
      if self <. other
      then Ordering_Less <: t_Ordering
      else if self >. other then Ordering_Greater <: t_Ordering else Ordering_Equal <: t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_33__from__cmp: t_Ord i8 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    _super_i1 = FStar.Tactics.Typeclasses.solve;
    f_cmp_pre = (fun (self: i8) (other: i8) -> true);
    f_cmp_post
    =
    (fun (self_: i8) (other: i8) (res: t_Ordering) ->
        match res <: t_Ordering with
        | Ordering_Less  -> self_ <. other
        | Ordering_Equal  -> self_ =. other
        | Ordering_Greater  -> self_ >. other);
    f_cmp
    =
    fun (self: i8) (other: i8) ->
      if self <. other
      then Ordering_Less <: t_Ordering
      else if self >. other then Ordering_Greater <: t_Ordering else Ordering_Equal <: t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_35__from__cmp: t_Ord u16 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    _super_i1 = FStar.Tactics.Typeclasses.solve;
    f_cmp_pre = (fun (self: u16) (other: u16) -> true);
    f_cmp_post
    =
    (fun (self_: u16) (other: u16) (res: t_Ordering) ->
        match res <: t_Ordering with
        | Ordering_Less  -> self_ <. other
        | Ordering_Equal  -> self_ =. other
        | Ordering_Greater  -> self_ >. other);
    f_cmp
    =
    fun (self: u16) (other: u16) ->
      if self <. other
      then Ordering_Less <: t_Ordering
      else if self >. other then Ordering_Greater <: t_Ordering else Ordering_Equal <: t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_37__from__cmp: t_Ord i16 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    _super_i1 = FStar.Tactics.Typeclasses.solve;
    f_cmp_pre = (fun (self: i16) (other: i16) -> true);
    f_cmp_post
    =
    (fun (self_: i16) (other: i16) (res: t_Ordering) ->
        match res <: t_Ordering with
        | Ordering_Less  -> self_ <. other
        | Ordering_Equal  -> self_ =. other
        | Ordering_Greater  -> self_ >. other);
    f_cmp
    =
    fun (self: i16) (other: i16) ->
      if self <. other
      then Ordering_Less <: t_Ordering
      else if self >. other then Ordering_Greater <: t_Ordering else Ordering_Equal <: t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_39__from__cmp: t_Ord u32 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    _super_i1 = FStar.Tactics.Typeclasses.solve;
    f_cmp_pre = (fun (self: u32) (other: u32) -> true);
    f_cmp_post
    =
    (fun (self_: u32) (other: u32) (res: t_Ordering) ->
        match res <: t_Ordering with
        | Ordering_Less  -> self_ <. other
        | Ordering_Equal  -> self_ =. other
        | Ordering_Greater  -> self_ >. other);
    f_cmp
    =
    fun (self: u32) (other: u32) ->
      if self <. other
      then Ordering_Less <: t_Ordering
      else if self >. other then Ordering_Greater <: t_Ordering else Ordering_Equal <: t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_41__from__cmp: t_Ord i32 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    _super_i1 = FStar.Tactics.Typeclasses.solve;
    f_cmp_pre = (fun (self: i32) (other: i32) -> true);
    f_cmp_post
    =
    (fun (self_: i32) (other: i32) (res: t_Ordering) ->
        match res <: t_Ordering with
        | Ordering_Less  -> self_ <. other
        | Ordering_Equal  -> self_ =. other
        | Ordering_Greater  -> self_ >. other);
    f_cmp
    =
    fun (self: i32) (other: i32) ->
      if self <. other
      then Ordering_Less <: t_Ordering
      else if self >. other then Ordering_Greater <: t_Ordering else Ordering_Equal <: t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_43__from__cmp: t_Ord u64 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    _super_i1 = FStar.Tactics.Typeclasses.solve;
    f_cmp_pre = (fun (self: u64) (other: u64) -> true);
    f_cmp_post
    =
    (fun (self_: u64) (other: u64) (res: t_Ordering) ->
        match res <: t_Ordering with
        | Ordering_Less  -> self_ <. other
        | Ordering_Equal  -> self_ =. other
        | Ordering_Greater  -> self_ >. other);
    f_cmp
    =
    fun (self: u64) (other: u64) ->
      if self <. other
      then Ordering_Less <: t_Ordering
      else if self >. other then Ordering_Greater <: t_Ordering else Ordering_Equal <: t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_45__from__cmp: t_Ord i64 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    _super_i1 = FStar.Tactics.Typeclasses.solve;
    f_cmp_pre = (fun (self: i64) (other: i64) -> true);
    f_cmp_post
    =
    (fun (self_: i64) (other: i64) (res: t_Ordering) ->
        match res <: t_Ordering with
        | Ordering_Less  -> self_ <. other
        | Ordering_Equal  -> self_ =. other
        | Ordering_Greater  -> self_ >. other);
    f_cmp
    =
    fun (self: i64) (other: i64) ->
      if self <. other
      then Ordering_Less <: t_Ordering
      else if self >. other then Ordering_Greater <: t_Ordering else Ordering_Equal <: t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_47__from__cmp: t_Ord u128 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    _super_i1 = FStar.Tactics.Typeclasses.solve;
    f_cmp_pre = (fun (self: u128) (other: u128) -> true);
    f_cmp_post
    =
    (fun (self_: u128) (other: u128) (res: t_Ordering) ->
        match res <: t_Ordering with
        | Ordering_Less  -> self_ <. other
        | Ordering_Equal  -> self_ =. other
        | Ordering_Greater  -> self_ >. other);
    f_cmp
    =
    fun (self: u128) (other: u128) ->
      if self <. other
      then Ordering_Less <: t_Ordering
      else if self >. other then Ordering_Greater <: t_Ordering else Ordering_Equal <: t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_49__from__cmp: t_Ord i128 =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    _super_i1 = FStar.Tactics.Typeclasses.solve;
    f_cmp_pre = (fun (self: i128) (other: i128) -> true);
    f_cmp_post
    =
    (fun (self_: i128) (other: i128) (res: t_Ordering) ->
        match res <: t_Ordering with
        | Ordering_Less  -> self_ <. other
        | Ordering_Equal  -> self_ =. other
        | Ordering_Greater  -> self_ >. other);
    f_cmp
    =
    fun (self: i128) (other: i128) ->
      if self <. other
      then Ordering_Less <: t_Ordering
      else if self >. other then Ordering_Greater <: t_Ordering else Ordering_Equal <: t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_51__from__cmp: t_Ord usize =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    _super_i1 = FStar.Tactics.Typeclasses.solve;
    f_cmp_pre = (fun (self: usize) (other: usize) -> true);
    f_cmp_post
    =
    (fun (self_: usize) (other: usize) (res: t_Ordering) ->
        match res <: t_Ordering with
        | Ordering_Less  -> self_ <. other
        | Ordering_Equal  -> self_ =. other
        | Ordering_Greater  -> self_ >. other);
    f_cmp
    =
    fun (self: usize) (other: usize) ->
      if self <. other
      then Ordering_Less <: t_Ordering
      else if self >. other then Ordering_Greater <: t_Ordering else Ordering_Equal <: t_Ordering
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_53__from__cmp: t_Ord isize =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    _super_i1 = FStar.Tactics.Typeclasses.solve;
    f_cmp_pre = (fun (self: isize) (other: isize) -> true);
    f_cmp_post
    =
    (fun (self_: isize) (other: isize) (res: t_Ordering) ->
        match res <: t_Ordering with
        | Ordering_Less  -> self_ <. other
        | Ordering_Equal  -> self_ =. other
        | Ordering_Greater  -> self_ >. other);
    f_cmp
    =
    fun (self: isize) (other: isize) ->
      if self <. other
      then Ordering_Less <: t_Ordering
      else if self >. other then Ordering_Greater <: t_Ordering else Ordering_Equal <: t_Ordering
  }

let max_by_key
      (#v_T #v_F #v_K: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Ord v_K)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_K})
      (v1 v2: v_T)
      (f: (v_T -> v_K))
    : v_T =
  if impl_54__is_lt (f_cmp #v_K #FStar.Tactics.Typeclasses.solve (f v2) (f v1) <: t_Ordering)
  then v1
  else v2

let min_by_key
      (#v_T #v_F #v_K: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Ord v_K)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_K})
      (v1 v2: v_T)
      (f: (v_T -> v_K))
    : v_T =
  if impl_54__is_lt (f_cmp #v_K #FStar.Tactics.Typeclasses.solve (f v2) (f v1) <: t_Ordering)
  then v2
  else v1

/// See [`std::cmp::minmax`]
let minmax (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Ord v_T) (v1 v2: v_T)
    : t_Array v_T (mk_usize 2) =
  if impl_54__is_lt (f_cmp #v_T #FStar.Tactics.Typeclasses.solve v2 v1 <: t_Ordering)
  then Rust_primitives.Slice.array_pair #v_T v2 v1
  else Rust_primitives.Slice.array_pair #v_T v1 v2

let minmax_by_key
      (#v_T #v_F #v_K: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Ord v_K)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_K})
      (v1 v2: v_T)
      (f: (v_T -> v_K))
    : t_Array v_T (mk_usize 2) =
  if impl_54__is_lt (f_cmp #v_K #FStar.Tactics.Typeclasses.solve (f v2) (f v1) <: t_Ordering)
  then Rust_primitives.Slice.array_pair #v_T v2 v1
  else Rust_primitives.Slice.array_pair #v_T v1 v2

/// See [`std::cmp::clamp`]
let clamp
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Ord v_T)
      (value min max: v_T)
    : Prims.Pure v_T
      (requires impl_54__is_le (f_cmp #v_T #FStar.Tactics.Typeclasses.solve min max <: t_Ordering))
      (fun _ -> Prims.l_True) =
  let _:Prims.unit =
    if
      ~.(impl_54__is_le (f_cmp #v_T #FStar.Tactics.Typeclasses.solve min max <: t_Ordering) <: bool)
    then Core_models.Panicking.Internal.panic #Prims.unit ()
  in
  match f_cmp #v_T #FStar.Tactics.Typeclasses.solve value min <: t_Ordering with
  | Ordering_Less  -> min
  | Ordering_Equal  -> value
  | Ordering_Greater  ->
    match f_cmp #v_T #FStar.Tactics.Typeclasses.solve value max <: t_Ordering with
    | Ordering_Greater  -> max
    | _ -> value

assume
val iter_min': #v_I: Type0 -> {| i0: t_Iterator v_I |} -> {| i1: t_Ord i0.f_Item |} -> iter: v_I
  -> t_Option i0.f_Item

unfold
let iter_min
      (#v_I: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Ord i0.f_Item)
     = iter_min' #v_I #i0 #i1

assume
val iter_max': #v_I: Type0 -> {| i0: t_Iterator v_I |} -> {| i1: t_Ord i0.f_Item |} -> iter: v_I
  -> t_Option i0.f_Item

unfold
let iter_max
      (#v_I: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Ord i0.f_Item)
     = iter_max' #v_I #i0 #i1

class t_RangeBoundsDefaults (v_Self: Type0) (v_T: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:t_RangeBounds v_Self v_T;
  f_contains_pre:
      #v_U: Type0 ->
      {| i1: t_PartialOrd v_T v_U |} ->
      {| i2: t_PartialOrd v_U v_T |} ->
      self_: v_Self ->
      item: v_U
    -> pred: Type0{true ==> pred};
  f_contains_post:
      #v_U: Type0 ->
      {| i1: t_PartialOrd v_T v_U |} ->
      {| i2: t_PartialOrd v_U v_T |} ->
      v_Self ->
      v_U ->
      bool
    -> Type0;
  f_contains:
      #v_U: Type0 ->
      {| i1: t_PartialOrd v_T v_U |} ->
      {| i2: t_PartialOrd v_U v_T |} ->
      x0: v_Self ->
      x1: v_U
    -> Prims.Pure bool
        (f_contains_pre #v_U #i1 #i2 x0 x1)
        (fun result -> f_contains_post #v_U #i1 #i2 x0 x1 result);
  f_is_empty_pre:{| i1: t_PartialOrd v_T v_T |} -> self_: v_Self -> pred: Type0{true ==> pred};
  f_is_empty_post:{| i1: t_PartialOrd v_T v_T |} -> v_Self -> bool -> Type0;
  f_is_empty:{| i1: t_PartialOrd v_T v_T |} -> x0: v_Self
    -> Prims.Pure bool (f_is_empty_pre #i1 x0) (fun result -> f_is_empty_post #i1 x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) (v_T:Type0) {|i: t_RangeBoundsDefaults v_Self v_T|} -> i._super_i0

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3__from__range
      (#v_T #v_R: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_RangeBounds v_R v_T)
    : t_RangeBoundsDefaults v_R v_T =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_contains_pre
    =
    (fun
        (#v_U: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_PartialOrd v_T v_U)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: t_PartialOrd v_U v_T)
        (self: v_R)
        (item: v_U)
        ->
        true);
    f_contains_post
    =
    (fun
        (#v_U: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_PartialOrd v_T v_U)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: t_PartialOrd v_U v_T)
        (self: v_R)
        (item: v_U)
        (out: bool)
        ->
        true);
    f_contains
    =
    (fun
        (#v_U: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_PartialOrd v_T v_U)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: t_PartialOrd v_U v_T)
        (self: v_R)
        (item: v_U)
        ->
        bounds_contain #v_T
          #v_U
          (f_start_bound #v_R #v_T #FStar.Tactics.Typeclasses.solve self <: t_Bound v_T)
          (f_end_bound #v_R #v_T #FStar.Tactics.Typeclasses.solve self <: t_Bound v_T)
          item);
    f_is_empty_pre
    =
    (fun (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_PartialOrd v_T v_T) (self: v_R) -> true);
    f_is_empty_post
    =
    (fun
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_PartialOrd v_T v_T)
        (self: v_R)
        (out: bool)
        ->
        true);
    f_is_empty
    =
    fun (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_PartialOrd v_T v_T) (self: v_R) ->
      bounds_are_empty #v_T
        (f_start_bound #v_R #v_T #FStar.Tactics.Typeclasses.solve self <: t_Bound v_T)
        (f_end_bound #v_R #v_T #FStar.Tactics.Typeclasses.solve self <: t_Bound v_T)
  }

let bounds_intersect
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Ord v_T)
      (a b: (t_Bound v_T & t_Bound v_T))
    : (t_Bound v_T & t_Bound v_T) =
  let (a_start: t_Bound v_T), (a_end: t_Bound v_T) = a in
  let (b_start: t_Bound v_T), (b_end: t_Bound v_T) = b in
  let start:t_Bound v_T =
    match a_start, b_start <: (t_Bound v_T & t_Bound v_T) with
    | Bound_Unbounded , y -> y
    | x, Bound_Unbounded  -> x
    | Bound_Included x, Bound_Included y -> Bound_Included (max #v_T x y) <: t_Bound v_T
    | Bound_Excluded x, Bound_Excluded y -> Bound_Excluded (max #v_T x y) <: t_Bound v_T
    | Bound_Included i, Bound_Excluded e
    | Bound_Excluded e, Bound_Included i ->
      if is_lt #v_T #v_T e i
      then Bound_Included i <: t_Bound v_T
      else Bound_Excluded e <: t_Bound v_T
  in
  let v_end:t_Bound v_T =
    match a_end, b_end <: (t_Bound v_T & t_Bound v_T) with
    | Bound_Unbounded , y -> y
    | x, Bound_Unbounded  -> x
    | Bound_Included x, Bound_Included y -> Bound_Included (min #v_T x y) <: t_Bound v_T
    | Bound_Excluded x, Bound_Excluded y -> Bound_Excluded (min #v_T x y) <: t_Bound v_T
    | Bound_Included i, Bound_Excluded e
    | Bound_Excluded e, Bound_Included i ->
      if is_lt #v_T #v_T i e
      then Bound_Included i <: t_Bound v_T
      else Bound_Excluded e <: t_Bound v_T
  in
  start, v_end <: (t_Bound v_T & t_Bound v_T)

class t_IteratorMethods (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:t_Iterator v_Self;
  f_fold_pre:
      #v_B: Type0 ->
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_F (v_B & (_super_i0).f_Item) |} ->
      v_Self ->
      v_B ->
      v_F
    -> Type0;
  f_fold_post:
      #v_B: Type0 ->
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_F (v_B & (_super_i0).f_Item) |} ->
      v_Self ->
      v_B ->
      v_F ->
      v_B
    -> Type0;
  f_fold:
      #v_B: Type0 ->
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_F (v_B & (_super_i0).f_Item) |} ->
      x0: v_Self ->
      x1: v_B ->
      x2: v_F
    -> Prims.Pure v_B
        (f_fold_pre #v_B #v_F #i1 x0 x1 x2)
        (fun result -> f_fold_post #v_B #v_F #i1 x0 x1 x2 result);
  f_enumerate_pre:v_Self -> Type0;
  f_enumerate_post:v_Self -> t_Enumerate v_Self -> Type0;
  f_enumerate:x0: v_Self
    -> Prims.Pure (t_Enumerate v_Self)
        (f_enumerate_pre x0)
        (fun result -> f_enumerate_post x0 result);
  f_step_by_pre:self_: v_Self -> step: usize -> pred: Type0{step >. mk_usize 0 ==> pred};
  f_step_by_post:v_Self -> usize -> t_StepBy v_Self -> Type0;
  f_step_by:x0: v_Self -> x1: usize
    -> Prims.Pure (t_StepBy v_Self)
        (f_step_by_pre x0 x1)
        (fun result -> f_step_by_post x0 x1 result);
  f_map_pre:
      #v_O: Type0 ->
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_F (_super_i0).f_Item |} ->
      v_Self ->
      v_F
    -> Type0;
  f_map_post:
      #v_O: Type0 ->
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_F (_super_i0).f_Item |} ->
      v_Self ->
      v_F ->
      t_Map v_Self v_F
    -> Type0;
  f_map:
      #v_O: Type0 ->
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_F (_super_i0).f_Item |} ->
      x0: v_Self ->
      x1: v_F
    -> Prims.Pure (t_Map v_Self v_F)
        (f_map_pre #v_O #v_F #i1 x0 x1)
        (fun result -> f_map_post #v_O #v_F #i1 x0 x1 result);
  f_all_pre:
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_F (_super_i0).f_Item |} ->
      v_Self ->
      v_F
    -> Type0;
  f_all_post:
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_F (_super_i0).f_Item |} ->
      v_Self ->
      v_F ->
      bool
    -> Type0;
  f_all:
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_F (_super_i0).f_Item |} ->
      x0: v_Self ->
      x1: v_F
    -> Prims.Pure bool (f_all_pre #v_F #i1 x0 x1) (fun result -> f_all_post #v_F #i1 x0 x1 result);
  f_take_pre:v_Self -> usize -> Type0;
  f_take_post:v_Self -> usize -> t_Take v_Self -> Type0;
  f_take:x0: v_Self -> x1: usize
    -> Prims.Pure (t_Take v_Self) (f_take_pre x0 x1) (fun result -> f_take_post x0 x1 result);
  f_flat_map_pre:
      #v_U: Type0 ->
      #v_F: Type0 ->
      {| i1: t_Iterator v_U |} ->
      {| i2: Core_models.Ops.Function.t_Fn v_F (_super_i0).f_Item |} ->
      v_Self ->
      v_F
    -> Type0;
  f_flat_map_post:
      #v_U: Type0 ->
      #v_F: Type0 ->
      {| i1: t_Iterator v_U |} ->
      {| i2: Core_models.Ops.Function.t_Fn v_F (_super_i0).f_Item |} ->
      v_Self ->
      v_F ->
      t_FlatMap v_Self v_U v_F
    -> Type0;
  f_flat_map:
      #v_U: Type0 ->
      #v_F: Type0 ->
      {| i1: t_Iterator v_U |} ->
      {| i2: Core_models.Ops.Function.t_Fn v_F (_super_i0).f_Item |} ->
      x0: v_Self ->
      x1: v_F
    -> Prims.Pure (t_FlatMap v_Self v_U v_F)
        (f_flat_map_pre #v_U #v_F #i1 #i2 x0 x1)
        (fun result -> f_flat_map_post #v_U #v_F #i1 #i2 x0 x1 result);
  f_flatten_pre:{| i1: t_Iterator (_super_i0).f_Item |} -> v_Self -> Type0;
  f_flatten_post:{| i1: t_Iterator (_super_i0).f_Item |} -> v_Self -> t_Flatten v_Self -> Type0;
  f_flatten:{| i1: t_Iterator (_super_i0).f_Item |} -> x0: v_Self
    -> Prims.Pure (t_Flatten v_Self)
        (f_flatten_pre #i1 x0)
        (fun result -> f_flatten_post #i1 x0 result);
  f_zip_pre:#v_I2: Type0 -> {| i1: t_Iterator v_I2 |} -> v_Self -> v_I2 -> Type0;
  f_zip_post:#v_I2: Type0 -> {| i1: t_Iterator v_I2 |} -> v_Self -> v_I2 -> t_Zip v_Self v_I2
    -> Type0;
  f_zip:#v_I2: Type0 -> {| i1: t_Iterator v_I2 |} -> x0: v_Self -> x1: v_I2
    -> Prims.Pure (t_Zip v_Self v_I2)
        (f_zip_pre #v_I2 #i1 x0 x1)
        (fun result -> f_zip_post #v_I2 #i1 x0 x1 result);
  f_filter_pre:
      #v_P: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_P (_super_i0).f_Item |} ->
      v_Self ->
      v_P
    -> Type0;
  f_filter_post:
      #v_P: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_P (_super_i0).f_Item |} ->
      v_Self ->
      v_P ->
      t_Filter v_Self v_P
    -> Type0;
  f_filter:
      #v_P: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_P (_super_i0).f_Item |} ->
      x0: v_Self ->
      x1: v_P
    -> Prims.Pure (t_Filter v_Self v_P)
        (f_filter_pre #v_P #i1 x0 x1)
        (fun result -> f_filter_post #v_P #i1 x0 x1 result);
  f_chain_pre:
      #v_U: Type0 ->
      {| i1: t_Iterator v_U |} ->
      #_: unit{i1.f_Item == (_super_i0).f_Item} ->
      v_Self ->
      v_U
    -> Type0;
  f_chain_post:
      #v_U: Type0 ->
      {| i1: t_Iterator v_U |} ->
      #_: unit{i1.f_Item == (_super_i0).f_Item} ->
      v_Self ->
      v_U ->
      t_Chain v_Self v_U
    -> Type0;
  f_chain:
      #v_U: Type0 ->
      {| i1: t_Iterator v_U |} ->
      #_: unit{i1.f_Item == (_super_i0).f_Item} ->
      x0: v_Self ->
      x1: v_U
    -> Prims.Pure (t_Chain v_Self v_U)
        (f_chain_pre #v_U #i1 #_ x0 x1)
        (fun result -> f_chain_post #v_U #i1 #_ x0 x1 result);
  f_skip_pre:v_Self -> usize -> Type0;
  f_skip_post:v_Self -> usize -> t_Skip v_Self -> Type0;
  f_skip:x0: v_Self -> x1: usize
    -> Prims.Pure (t_Skip v_Self) (f_skip_pre x0 x1) (fun result -> f_skip_post x0 x1 result);
  f_any_pre:
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_F (_super_i0).f_Item |} ->
      v_Self ->
      v_F
    -> Type0;
  f_any_post:
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_F (_super_i0).f_Item |} ->
      v_Self ->
      v_F ->
      bool
    -> Type0;
  f_any:
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_F (_super_i0).f_Item |} ->
      x0: v_Self ->
      x1: v_F
    -> Prims.Pure bool (f_any_pre #v_F #i1 x0 x1) (fun result -> f_any_post #v_F #i1 x0 x1 result);
  f_find_pre:
      #v_P: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_P (_super_i0).f_Item |} ->
      v_Self ->
      v_P
    -> Type0;
  f_find_post:
      #v_P: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_P (_super_i0).f_Item |} ->
      v_Self ->
      v_P ->
      t_Option (_super_i0).f_Item
    -> Type0;
  f_find:
      #v_P: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_P (_super_i0).f_Item |} ->
      x0: v_Self ->
      x1: v_P
    -> Prims.Pure (t_Option (_super_i0).f_Item)
        (f_find_pre #v_P #i1 x0 x1)
        (fun result -> f_find_post #v_P #i1 x0 x1 result);
  f_find_map_pre:
      #v_B: Type0 ->
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_F (_super_i0).f_Item |} ->
      v_Self ->
      v_F
    -> Type0;
  f_find_map_post:
      #v_B: Type0 ->
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_F (_super_i0).f_Item |} ->
      v_Self ->
      v_F ->
      t_Option v_B
    -> Type0;
  f_find_map:
      #v_B: Type0 ->
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_F (_super_i0).f_Item |} ->
      x0: v_Self ->
      x1: v_F
    -> Prims.Pure (t_Option v_B)
        (f_find_map_pre #v_B #v_F #i1 x0 x1)
        (fun result -> f_find_map_post #v_B #v_F #i1 x0 x1 result);
  f_position_pre:
      #v_P: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_P (_super_i0).f_Item |} ->
      v_Self ->
      v_P
    -> Type0;
  f_position_post:
      #v_P: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_P (_super_i0).f_Item |} ->
      v_Self ->
      v_P ->
      t_Option usize
    -> Type0;
  f_position:
      #v_P: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_P (_super_i0).f_Item |} ->
      x0: v_Self ->
      x1: v_P
    -> Prims.Pure (t_Option usize)
        (f_position_pre #v_P #i1 x0 x1)
        (fun result -> f_position_post #v_P #i1 x0 x1 result);
  f_count_pre:v_Self -> Type0;
  f_count_post:v_Self -> usize -> Type0;
  f_count:x0: v_Self -> Prims.Pure usize (f_count_pre x0) (fun result -> f_count_post x0 result);
  f_nth_pre:v_Self -> usize -> Type0;
  f_nth_post:v_Self -> usize -> t_Option (_super_i0).f_Item -> Type0;
  f_nth:x0: v_Self -> x1: usize
    -> Prims.Pure (t_Option (_super_i0).f_Item)
        (f_nth_pre x0 x1)
        (fun result -> f_nth_post x0 x1 result);
  f_last_pre:v_Self -> Type0;
  f_last_post:v_Self -> t_Option (_super_i0).f_Item -> Type0;
  f_last:x0: v_Self
    -> Prims.Pure (t_Option (_super_i0).f_Item)
        (f_last_pre x0)
        (fun result -> f_last_post x0 result);
  f_for_each_pre:
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_F (_super_i0).f_Item |} ->
      v_Self ->
      v_F
    -> Type0;
  f_for_each_post:
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_F (_super_i0).f_Item |} ->
      v_Self ->
      v_F ->
      Prims.unit
    -> Type0;
  f_for_each:
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_F (_super_i0).f_Item |} ->
      x0: v_Self ->
      x1: v_F
    -> Prims.Pure Prims.unit
        (f_for_each_pre #v_F #i1 x0 x1)
        (fun result -> f_for_each_post #v_F #i1 x0 x1 result);
  f_reduce_pre:
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_F ((_super_i0).f_Item & (_super_i0).f_Item) |} ->
      v_Self ->
      v_F
    -> Type0;
  f_reduce_post:
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_F ((_super_i0).f_Item & (_super_i0).f_Item) |} ->
      v_Self ->
      v_F ->
      t_Option (_super_i0).f_Item
    -> Type0;
  f_reduce:
      #v_F: Type0 ->
      {| i1: Core_models.Ops.Function.t_Fn v_F ((_super_i0).f_Item & (_super_i0).f_Item) |} ->
      x0: v_Self ->
      x1: v_F
    -> Prims.Pure (t_Option (_super_i0).f_Item)
        (f_reduce_pre #v_F #i1 x0 x1)
        (fun result -> f_reduce_post #v_F #i1 x0 x1 result);
  f_min_pre:{| i1: t_Ord (_super_i0).f_Item |} -> v_Self -> Type0;
  f_min_post:{| i1: t_Ord (_super_i0).f_Item |} -> v_Self -> t_Option (_super_i0).f_Item -> Type0;
  f_min:{| i1: t_Ord (_super_i0).f_Item |} -> x0: v_Self
    -> Prims.Pure (t_Option (_super_i0).f_Item)
        (f_min_pre #i1 x0)
        (fun result -> f_min_post #i1 x0 result);
  f_max_pre:{| i1: t_Ord (_super_i0).f_Item |} -> v_Self -> Type0;
  f_max_post:{| i1: t_Ord (_super_i0).f_Item |} -> v_Self -> t_Option (_super_i0).f_Item -> Type0;
  f_max:{| i1: t_Ord (_super_i0).f_Item |} -> x0: v_Self
    -> Prims.Pure (t_Option (_super_i0).f_Item)
        (f_max_pre #i1 x0)
        (fun result -> f_max_post #i1 x0 result);
  f_collect_pre:
      #v_B: Type0 ->
      {| i1: Core_models.Iter.Traits.Collect.t_FromIterator v_B (_super_i0).f_Item |} ->
      v_Self
    -> Type0;
  f_collect_post:
      #v_B: Type0 ->
      {| i1: Core_models.Iter.Traits.Collect.t_FromIterator v_B (_super_i0).f_Item |} ->
      v_Self ->
      v_B
    -> Type0;
  f_collect:
      #v_B: Type0 ->
      {| i1: Core_models.Iter.Traits.Collect.t_FromIterator v_B (_super_i0).f_Item |} ->
      x0: v_Self
    -> Prims.Pure v_B (f_collect_pre #v_B #i1 x0) (fun result -> f_collect_post #v_B #i1 x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_IteratorMethods v_Self|} -> i._super_i0

class t_IntoBoundsDefaults (v_Self: Type0) (v_T: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:t_IntoBounds v_Self v_T;
  f_intersect_pre:
      #v_R: Type0 ->
      {| i1: t_IntoBounds v_R v_T |} ->
      {| i2: t_Ord v_T |} ->
      self_: v_Self ->
      other: v_R
    -> pred: Type0{true ==> pred};
  f_intersect_post:
      #v_R: Type0 ->
      {| i1: t_IntoBounds v_R v_T |} ->
      {| i2: t_Ord v_T |} ->
      v_Self ->
      v_R ->
      (t_Bound v_T & t_Bound v_T)
    -> Type0;
  f_intersect:
      #v_R: Type0 ->
      {| i1: t_IntoBounds v_R v_T |} ->
      {| i2: t_Ord v_T |} ->
      x0: v_Self ->
      x1: v_R
    -> Prims.Pure (t_Bound v_T & t_Bound v_T)
        (f_intersect_pre #v_R #i1 #i2 x0 x1)
        (fun result -> f_intersect_post #v_R #i1 #i2 x0 x1 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) (v_T:Type0) {|i: t_IntoBoundsDefaults v_Self v_T|} -> i._super_i0

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl__from__iterator
      (#v_I: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Iterator v_I)
    : t_IteratorMethods v_I =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_fold_pre
    =
    (fun
        (#v_B: Type0)
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Ops.Function.t_Fn v_F (v_B & i0.f_Item))
        (self: v_I)
        (init: v_B)
        (f: v_F)
        ->
        true);
    f_fold_post
    =
    (fun
        (#v_B: Type0)
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Ops.Function.t_Fn v_F (v_B & i0.f_Item))
        (self: v_I)
        (init: v_B)
        (f: v_F)
        (out: v_B)
        ->
        true);
    f_fold
    =
    (fun
        (#v_B: Type0)
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Ops.Function.t_Fn v_F (v_B & i0.f_Item))
        (self: v_I)
        (init: v_B)
        (f: v_F)
        ->
        iter_fold #v_I #v_B #v_F self init f);
    f_enumerate_pre = (fun (self: v_I) -> true);
    f_enumerate_post = (fun (self: v_I) (out: t_Enumerate v_I) -> true);
    f_enumerate = (fun (self: v_I) -> impl__new #v_I self);
    f_step_by_pre = (fun (self_: v_I) (step: usize) -> step >. mk_usize 0);
    f_step_by_post = (fun (self: v_I) (step: usize) (out: t_StepBy v_I) -> true);
    f_step_by = (fun (self: v_I) (step: usize) -> impl__new__from__step_by #v_I self step);
    f_map_pre
    =
    (fun
        (#v_O: Type0)
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        ->
        true);
    f_map_post
    =
    (fun
        (#v_O: Type0)
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        (out: t_Map v_I v_F)
        ->
        true);
    f_map
    =
    (fun
        (#v_O: Type0)
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        ->
        impl__new__from__map #v_I #v_F self f);
    f_all_pre
    =
    (fun
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        ->
        true);
    f_all_post
    =
    (fun
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        (out: bool)
        ->
        true);
    f_all
    =
    (fun
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        ->
        iter_all #v_I #v_F self f);
    f_take_pre = (fun (self: v_I) (n: usize) -> true);
    f_take_post = (fun (self: v_I) (n: usize) (out: t_Take v_I) -> true);
    f_take = (fun (self: v_I) (n: usize) -> impl__new__from__take #v_I self n);
    f_flat_map_pre
    =
    (fun
        (#v_U: Type0)
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator v_U)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        ->
        true);
    f_flat_map_post
    =
    (fun
        (#v_U: Type0)
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator v_U)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        (out: t_FlatMap v_I v_U v_F)
        ->
        true);
    f_flat_map
    =
    (fun
        (#v_U: Type0)
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator v_U)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        ->
        impl__new__from__flat_map #v_I #v_U #v_F self f);
    f_flatten_pre
    =
    (fun (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator i0.f_Item) (self: v_I) -> true);
    f_flatten_post
    =
    (fun
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator i0.f_Item)
        (self: v_I)
        (out: t_Flatten v_I)
        ->
        true);
    f_flatten
    =
    (fun (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator i0.f_Item) (self: v_I) ->
        impl__new__from__flatten #v_I self);
    f_zip_pre
    =
    (fun
        (#v_I2: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator v_I2)
        (self: v_I)
        (it2: v_I2)
        ->
        true);
    f_zip_post
    =
    (fun
        (#v_I2: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator v_I2)
        (self: v_I)
        (it2: v_I2)
        (out: t_Zip v_I v_I2)
        ->
        true);
    f_zip
    =
    (fun
        (#v_I2: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator v_I2)
        (self: v_I)
        (it2: v_I2)
        ->
        impl__new__from__zip #v_I #v_I2 self it2);
    f_filter_pre
    =
    (fun
        (#v_P: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_P i0.f_Item)
        (self: v_I)
        (predicate: v_P)
        ->
        true);
    f_filter_post
    =
    (fun
        (#v_P: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_P i0.f_Item)
        (self: v_I)
        (predicate: v_P)
        (out: t_Filter v_I v_P)
        ->
        true);
    f_filter
    =
    (fun
        (#v_P: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_P i0.f_Item)
        (self: v_I)
        (predicate: v_P)
        ->
        impl__new__from__filter #v_I #v_P self predicate);
    f_chain_pre
    =
    (fun
        (#v_U: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator v_U)
        (self: v_I)
        (other: v_U)
        ->
        true);
    f_chain_post
    =
    (fun
        (#v_U: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator v_U)
        (self: v_I)
        (other: v_U)
        (out: t_Chain v_I v_U)
        ->
        true);
    f_chain
    =
    (fun
        (#v_U: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Iterator v_U)
        (self: v_I)
        (other: v_U)
        ->
        impl__new__from__chain #v_I #v_U self other);
    f_skip_pre = (fun (self: v_I) (n: usize) -> true);
    f_skip_post = (fun (self: v_I) (n: usize) (out: t_Skip v_I) -> true);
    f_skip = (fun (self: v_I) (n: usize) -> impl__new__from__skip #v_I self n);
    f_any_pre
    =
    (fun
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        ->
        true);
    f_any_post
    =
    (fun
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        (out: bool)
        ->
        true);
    f_any
    =
    (fun
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        ->
        iter_any #v_I #v_F self f);
    f_find_pre
    =
    (fun
        (#v_P: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_P i0.f_Item)
        (self: v_I)
        (predicate: v_P)
        ->
        true);
    f_find_post
    =
    (fun
        (#v_P: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_P i0.f_Item)
        (self: v_I)
        (predicate: v_P)
        (out1: t_Option i0.f_Item)
        ->
        true);
    f_find
    =
    (fun
        (#v_P: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_P i0.f_Item)
        (self: v_I)
        (predicate: v_P)
        ->
        let (tmp0: v_I), (out: t_Option i0.f_Item) = iter_find #v_I #v_P self predicate in
        let self:v_I = tmp0 in
        out);
    f_find_map_pre
    =
    (fun
        (#v_B: Type0)
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        ->
        true);
    f_find_map_post
    =
    (fun
        (#v_B: Type0)
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        (out: t_Option v_B)
        ->
        true);
    f_find_map
    =
    (fun
        (#v_B: Type0)
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        ->
        iter_find_map #v_I #v_B #v_F self f);
    f_position_pre
    =
    (fun
        (#v_P: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_P i0.f_Item)
        (self: v_I)
        (predicate: v_P)
        ->
        true);
    f_position_post
    =
    (fun
        (#v_P: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_P i0.f_Item)
        (self: v_I)
        (predicate: v_P)
        (out: t_Option usize)
        ->
        true);
    f_position
    =
    (fun
        (#v_P: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_P i0.f_Item)
        (self: v_I)
        (predicate: v_P)
        ->
        iter_position #v_I #v_P self predicate);
    f_count_pre = (fun (self: v_I) -> true);
    f_count_post = (fun (self: v_I) (out: usize) -> true);
    f_count = (fun (self: v_I) -> iter_count #v_I self);
    f_nth_pre = (fun (self: v_I) (n: usize) -> true);
    f_nth_post = (fun (self: v_I) (n: usize) (out: t_Option i0.f_Item) -> true);
    f_nth = (fun (self: v_I) (n: usize) -> iter_nth #v_I self n);
    f_last_pre = (fun (self: v_I) -> true);
    f_last_post = (fun (self: v_I) (out: t_Option i0.f_Item) -> true);
    f_last = (fun (self: v_I) -> iter_last #v_I self);
    f_for_each_pre
    =
    (fun
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        ->
        true);
    f_for_each_post
    =
    (fun
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        (out: Prims.unit)
        ->
        true);
    f_for_each
    =
    (fun
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F i0.f_Item)
        (self: v_I)
        (f: v_F)
        ->
        iter_for_each #v_I #v_F self f);
    f_reduce_pre
    =
    (fun
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Ops.Function.t_Fn v_F (i0.f_Item & i0.f_Item))
        (self: v_I)
        (f: v_F)
        ->
        true);
    f_reduce_post
    =
    (fun
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Ops.Function.t_Fn v_F (i0.f_Item & i0.f_Item))
        (self: v_I)
        (f: v_F)
        (out: t_Option i0.f_Item)
        ->
        true);
    f_reduce
    =
    (fun
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Ops.Function.t_Fn v_F (i0.f_Item & i0.f_Item))
        (self: v_I)
        (f: v_F)
        ->
        iter_reduce #v_I #v_F self f);
    f_min_pre
    =
    (fun (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Ord i0.f_Item) (self: v_I) -> true);
    f_min_post
    =
    (fun
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Ord i0.f_Item)
        (self: v_I)
        (out: t_Option i0.f_Item)
        ->
        true);
    f_min
    =
    (fun (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Ord i0.f_Item) (self: v_I) ->
        iter_min #v_I self);
    f_max_pre
    =
    (fun (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Ord i0.f_Item) (self: v_I) -> true);
    f_max_post
    =
    (fun
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Ord i0.f_Item)
        (self: v_I)
        (out: t_Option i0.f_Item)
        ->
        true);
    f_max
    =
    (fun (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Ord i0.f_Item) (self: v_I) ->
        iter_max #v_I self);
    f_collect_pre
    =
    (fun
        (#v_B: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Iter.Traits.Collect.t_FromIterator v_B i0.f_Item)
        (self: v_I)
        ->
        true);
    f_collect_post
    =
    (fun
        (#v_B: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Core_models.Iter.Traits.Collect.t_FromIterator v_B i0.f_Item)
        (self: v_I)
        (out: v_B)
        ->
        true);
    f_collect
    =
    fun
      (#v_B: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
        i1:
        Core_models.Iter.Traits.Collect.t_FromIterator v_B i0.f_Item)
      (self: v_I)
      ->
      Core_models.Iter.Traits.Collect.f_from_iter #v_B
        #i0.f_Item
        #FStar.Tactics.Typeclasses.solve
        #v_I
        self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4__from__range
      (#v_T #v_S: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_IntoBounds v_S v_T)
    : t_IntoBoundsDefaults v_S v_T =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_intersect_pre
    =
    (fun
        (#v_R: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_IntoBounds v_R v_T)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: t_Ord v_T)
        (self: v_S)
        (other: v_R)
        ->
        true);
    f_intersect_post
    =
    (fun
        (#v_R: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_IntoBounds v_R v_T)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: t_Ord v_T)
        (self: v_S)
        (other: v_R)
        (out: (t_Bound v_T & t_Bound v_T))
        ->
        true);
    f_intersect
    =
    fun
      (#v_R: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_IntoBounds v_R v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: t_Ord v_T)
      (self: v_S)
      (other: v_R)
      ->
      bounds_intersect #v_T
        (f_into_bounds #v_S #v_T #FStar.Tactics.Typeclasses.solve self
          <:
          (t_Bound v_T & t_Bound v_T))
        (f_into_bounds #v_R #v_T #FStar.Tactics.Typeclasses.solve other
          <:
          (t_Bound v_T & t_Bound v_T))
  }
