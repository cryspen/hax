module Core_models.Convert
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul

class t_Into (v_Self: Type0) (v_T: Type0) = {
  f_into_pre:self_: v_Self -> pred: Type0{true ==> pred};
  f_into_post:v_Self -> v_T -> Type0;
  f_into:x0: v_Self -> Prims.Pure v_T (f_into_pre x0) (fun result -> f_into_post x0 result)
}

class t_From (v_Self: Type0) (v_T: Type0) = {
  f_from_pre:x: v_T -> pred: Type0{true ==> pred};
  f_from_post:v_T -> v_Self -> Type0;
  f_from:x0: v_T -> Prims.Pure v_Self (f_from_pre x0) (fun result -> f_from_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_T #v_U: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_From v_U v_T)
    : t_Into v_T v_U =
  {
    f_into_pre = (fun (self: v_T) -> true);
    f_into_post = (fun (self: v_T) (out: v_U) -> true);
    f_into = fun (self: v_T) -> f_from #v_U #v_T #FStar.Tactics.Typeclasses.solve self
  }

type t_Infallible = | Infallible : t_Infallible

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4 (#v_T: Type0) : t_From v_T v_T =
  {
    f_from_pre = (fun (x: v_T) -> true);
    f_from_post = (fun (x: v_T) (out: v_T) -> true);
    f_from = fun (x: v_T) -> x
  }

class t_AsRef (v_Self: Type0) (v_T: Type0) = {
  f_as_ref_pre:v_Self -> Type0;
  f_as_ref_post:v_Self -> v_T -> Type0;
  f_as_ref:x0: v_Self -> Prims.Pure v_T (f_as_ref_pre x0) (fun result -> f_as_ref_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5 (#v_T: Type0) : t_AsRef v_T v_T =
  {
    f_as_ref_pre = (fun (self: v_T) -> true);
    f_as_ref_post = (fun (self: v_T) (out: v_T) -> true);
    f_as_ref = fun (self: v_T) -> self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6: t_From u16 u8 =
  {
    f_from_pre = (fun (x: u8) -> true);
    f_from_post = (fun (x: u8) (out: u16) -> true);
    f_from = fun (x: u8) -> cast (x <: u8) <: u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7: t_From u32 u8 =
  {
    f_from_pre = (fun (x: u8) -> true);
    f_from_post = (fun (x: u8) (out: u32) -> true);
    f_from = fun (x: u8) -> cast (x <: u8) <: u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8: t_From u32 u16 =
  {
    f_from_pre = (fun (x: u16) -> true);
    f_from_post = (fun (x: u16) (out: u32) -> true);
    f_from = fun (x: u16) -> cast (x <: u16) <: u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9: t_From u64 u8 =
  {
    f_from_pre = (fun (x: u8) -> true);
    f_from_post = (fun (x: u8) (out: u64) -> true);
    f_from = fun (x: u8) -> cast (x <: u8) <: u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10: t_From u64 u16 =
  {
    f_from_pre = (fun (x: u16) -> true);
    f_from_post = (fun (x: u16) (out: u64) -> true);
    f_from = fun (x: u16) -> cast (x <: u16) <: u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_11: t_From u64 u32 =
  {
    f_from_pre = (fun (x: u32) -> true);
    f_from_post = (fun (x: u32) (out: u64) -> true);
    f_from = fun (x: u32) -> cast (x <: u32) <: u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_12: t_From u64 usize =
  {
    f_from_pre = (fun (x: usize) -> true);
    f_from_post = (fun (x: usize) (out: u64) -> true);
    f_from = fun (x: usize) -> cast (x <: usize) <: u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_13: t_From u128 u8 =
  {
    f_from_pre = (fun (x: u8) -> true);
    f_from_post = (fun (x: u8) (out: u128) -> true);
    f_from = fun (x: u8) -> cast (x <: u8) <: u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_14: t_From u128 u16 =
  {
    f_from_pre = (fun (x: u16) -> true);
    f_from_post = (fun (x: u16) (out: u128) -> true);
    f_from = fun (x: u16) -> cast (x <: u16) <: u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_15: t_From u128 u32 =
  {
    f_from_pre = (fun (x: u32) -> true);
    f_from_post = (fun (x: u32) (out: u128) -> true);
    f_from = fun (x: u32) -> cast (x <: u32) <: u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_16: t_From u128 u64 =
  {
    f_from_pre = (fun (x: u64) -> true);
    f_from_post = (fun (x: u64) (out: u128) -> true);
    f_from = fun (x: u64) -> cast (x <: u64) <: u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_17: t_From u128 usize =
  {
    f_from_pre = (fun (x: usize) -> true);
    f_from_post = (fun (x: usize) (out: u128) -> true);
    f_from = fun (x: usize) -> cast (x <: usize) <: u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_18: t_From usize u8 =
  {
    f_from_pre = (fun (x: u8) -> true);
    f_from_post = (fun (x: u8) (out: usize) -> true);
    f_from = fun (x: u8) -> cast (x <: u8) <: usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_19: t_From usize u16 =
  {
    f_from_pre = (fun (x: u16) -> true);
    f_from_post = (fun (x: u16) (out: usize) -> true);
    f_from = fun (x: u16) -> cast (x <: u16) <: usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_20: t_From usize u32 =
  {
    f_from_pre = (fun (x: u32) -> true);
    f_from_post = (fun (x: u32) (out: usize) -> true);
    f_from = fun (x: u32) -> cast (x <: u32) <: usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_21: t_From i16 i8 =
  {
    f_from_pre = (fun (x: i8) -> true);
    f_from_post = (fun (x: i8) (out: i16) -> true);
    f_from = fun (x: i8) -> cast (x <: i8) <: i16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_22: t_From i32 i8 =
  {
    f_from_pre = (fun (x: i8) -> true);
    f_from_post = (fun (x: i8) (out: i32) -> true);
    f_from = fun (x: i8) -> cast (x <: i8) <: i32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_23: t_From i32 i16 =
  {
    f_from_pre = (fun (x: i16) -> true);
    f_from_post = (fun (x: i16) (out: i32) -> true);
    f_from = fun (x: i16) -> cast (x <: i16) <: i32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_24: t_From i64 i8 =
  {
    f_from_pre = (fun (x: i8) -> true);
    f_from_post = (fun (x: i8) (out: i64) -> true);
    f_from = fun (x: i8) -> cast (x <: i8) <: i64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_25: t_From i64 i16 =
  {
    f_from_pre = (fun (x: i16) -> true);
    f_from_post = (fun (x: i16) (out: i64) -> true);
    f_from = fun (x: i16) -> cast (x <: i16) <: i64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_26: t_From i64 i32 =
  {
    f_from_pre = (fun (x: i32) -> true);
    f_from_post = (fun (x: i32) (out: i64) -> true);
    f_from = fun (x: i32) -> cast (x <: i32) <: i64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_27: t_From i64 isize =
  {
    f_from_pre = (fun (x: isize) -> true);
    f_from_post = (fun (x: isize) (out: i64) -> true);
    f_from = fun (x: isize) -> cast (x <: isize) <: i64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_28: t_From i128 i8 =
  {
    f_from_pre = (fun (x: i8) -> true);
    f_from_post = (fun (x: i8) (out: i128) -> true);
    f_from = fun (x: i8) -> cast (x <: i8) <: i128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_29: t_From i128 i16 =
  {
    f_from_pre = (fun (x: i16) -> true);
    f_from_post = (fun (x: i16) (out: i128) -> true);
    f_from = fun (x: i16) -> cast (x <: i16) <: i128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_30: t_From i128 i32 =
  {
    f_from_pre = (fun (x: i32) -> true);
    f_from_post = (fun (x: i32) (out: i128) -> true);
    f_from = fun (x: i32) -> cast (x <: i32) <: i128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_31: t_From i128 i64 =
  {
    f_from_pre = (fun (x: i64) -> true);
    f_from_post = (fun (x: i64) (out: i128) -> true);
    f_from = fun (x: i64) -> cast (x <: i64) <: i128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_32: t_From i128 isize =
  {
    f_from_pre = (fun (x: isize) -> true);
    f_from_post = (fun (x: isize) (out: i128) -> true);
    f_from = fun (x: isize) -> cast (x <: isize) <: i128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_33: t_From isize i8 =
  {
    f_from_pre = (fun (x: i8) -> true);
    f_from_post = (fun (x: i8) (out: isize) -> true);
    f_from = fun (x: i8) -> cast (x <: i8) <: isize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_34: t_From isize i16 =
  {
    f_from_pre = (fun (x: i16) -> true);
    f_from_post = (fun (x: i16) (out: isize) -> true);
    f_from = fun (x: i16) -> cast (x <: i16) <: isize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_35: t_From isize i32 =
  {
    f_from_pre = (fun (x: i32) -> true);
    f_from_post = (fun (x: i32) (out: isize) -> true);
    f_from = fun (x: i32) -> cast (x <: i32) <: isize
  }

class t_TryInto (v_Self: Type0) (v_T: Type0) = {
  f_Error:Type0;
  f_try_into_pre:self_: v_Self -> pred: Type0{true ==> pred};
  f_try_into_post:v_Self -> Core_models.Result.t_Result v_T f_Error -> Type0;
  f_try_into:x0: v_Self
    -> Prims.Pure (Core_models.Result.t_Result v_T f_Error)
        (f_try_into_pre x0)
        (fun result -> f_try_into_post x0 result)
}

class t_TryFrom (v_Self: Type0) (v_T: Type0) = {
  f_Error:Type0;
  f_try_from_pre:x: v_T -> pred: Type0{true ==> pred};
  f_try_from_post:v_T -> Core_models.Result.t_Result v_Self f_Error -> Type0;
  f_try_from:x0: v_T
    -> Prims.Pure (Core_models.Result.t_Result v_Self f_Error)
        (f_try_from_pre x0)
        (fun result -> f_try_from_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1 (#v_T #v_U: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_From v_U v_T)
    : t_TryFrom v_U v_T =
  {
    f_Error = t_Infallible;
    f_try_from_pre = (fun (x: v_T) -> true);
    f_try_from_post = (fun (x: v_T) (out: Core_models.Result.t_Result v_U t_Infallible) -> true);
    f_try_from
    =
    fun (x: v_T) ->
      Core_models.Result.Result_Ok (f_from #v_U #v_T #FStar.Tactics.Typeclasses.solve x)
      <:
      Core_models.Result.t_Result v_U t_Infallible
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2
      (#v_T: Type0)
      (v_N: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Marker.t_Copy v_T)
    : t_TryFrom (t_Array v_T v_N) (t_Slice v_T) =
  {
    f_Error = Core_models.Array.t_TryFromSliceError;
    f_try_from_pre = (fun (x: t_Slice v_T) -> true);
    f_try_from_post
    =
    (fun
        (x: t_Slice v_T)
        (out: Core_models.Result.t_Result (t_Array v_T v_N) Core_models.Array.t_TryFromSliceError)
        ->
        true);
    f_try_from
    =
    fun (x: t_Slice v_T) ->
      if (Core_models.Slice.impl__len #v_T x <: usize) =. v_N
      then
        Core_models.Result.Result_Ok
        (Rust_primitives.Slice.array_from_fn #v_T
            v_N
            (fun i ->
                let i:usize = i in
                Rust_primitives.Slice.slice_index #v_T x i <: v_T))
        <:
        Core_models.Result.t_Result (t_Array v_T v_N) Core_models.Array.t_TryFromSliceError
      else
        Core_models.Result.Result_Err
        (Core_models.Array.TryFromSliceError <: Core_models.Array.t_TryFromSliceError)
        <:
        Core_models.Result.t_Result (t_Array v_T v_N) Core_models.Array.t_TryFromSliceError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3 (#v_T #v_U: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_TryFrom v_U v_T)
    : t_TryInto v_T v_U =
  {
    f_Error = i0.f_Error;
    f_try_into_pre = (fun (self: v_T) -> true);
    f_try_into_post = (fun (self: v_T) (out: Core_models.Result.t_Result v_U i0.f_Error) -> true);
    f_try_into = fun (self: v_T) -> f_try_from #v_U #v_T #FStar.Tactics.Typeclasses.solve self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_36: t_TryFrom u8 u16 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: u16) -> true);
    f_try_from_post
    =
    (fun (x: u16) (out: Core_models.Result.t_Result u8 Core_models.Num.Error.t_TryFromIntError) ->
        true);
    f_try_from
    =
    fun (x: u16) ->
      if
        x >. (cast (Core_models.Num.impl_u8__MAX <: u8) <: u16) ||
        x <. (cast (Core_models.Num.impl_u8__MIN <: u8) <: u16)
      then
        Core_models.Result.Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        Core_models.Result.t_Result u8 Core_models.Num.Error.t_TryFromIntError
      else
        Core_models.Result.Result_Ok (cast (x <: u16) <: u8)
        <:
        Core_models.Result.t_Result u8 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_37: t_TryFrom u8 u32 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: u32) -> true);
    f_try_from_post
    =
    (fun (x: u32) (out: Core_models.Result.t_Result u8 Core_models.Num.Error.t_TryFromIntError) ->
        true);
    f_try_from
    =
    fun (x: u32) ->
      if
        x >. (cast (Core_models.Num.impl_u8__MAX <: u8) <: u32) ||
        x <. (cast (Core_models.Num.impl_u8__MIN <: u8) <: u32)
      then
        Core_models.Result.Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        Core_models.Result.t_Result u8 Core_models.Num.Error.t_TryFromIntError
      else
        Core_models.Result.Result_Ok (cast (x <: u32) <: u8)
        <:
        Core_models.Result.t_Result u8 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_38: t_TryFrom u16 u32 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: u32) -> true);
    f_try_from_post
    =
    (fun (x: u32) (out: Core_models.Result.t_Result u16 Core_models.Num.Error.t_TryFromIntError) ->
        true);
    f_try_from
    =
    fun (x: u32) ->
      if
        x >. (cast (Core_models.Num.impl_u16__MAX <: u16) <: u32) ||
        x <. (cast (Core_models.Num.impl_u16__MIN <: u16) <: u32)
      then
        Core_models.Result.Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        Core_models.Result.t_Result u16 Core_models.Num.Error.t_TryFromIntError
      else
        Core_models.Result.Result_Ok (cast (x <: u32) <: u16)
        <:
        Core_models.Result.t_Result u16 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_39: t_TryFrom u8 u64 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: u64) -> true);
    f_try_from_post
    =
    (fun (x: u64) (out: Core_models.Result.t_Result u8 Core_models.Num.Error.t_TryFromIntError) ->
        true);
    f_try_from
    =
    fun (x: u64) ->
      if
        x >. (cast (Core_models.Num.impl_u8__MAX <: u8) <: u64) ||
        x <. (cast (Core_models.Num.impl_u8__MIN <: u8) <: u64)
      then
        Core_models.Result.Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        Core_models.Result.t_Result u8 Core_models.Num.Error.t_TryFromIntError
      else
        Core_models.Result.Result_Ok (cast (x <: u64) <: u8)
        <:
        Core_models.Result.t_Result u8 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_40: t_TryFrom u16 u64 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: u64) -> true);
    f_try_from_post
    =
    (fun (x: u64) (out: Core_models.Result.t_Result u16 Core_models.Num.Error.t_TryFromIntError) ->
        true);
    f_try_from
    =
    fun (x: u64) ->
      if
        x >. (cast (Core_models.Num.impl_u16__MAX <: u16) <: u64) ||
        x <. (cast (Core_models.Num.impl_u16__MIN <: u16) <: u64)
      then
        Core_models.Result.Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        Core_models.Result.t_Result u16 Core_models.Num.Error.t_TryFromIntError
      else
        Core_models.Result.Result_Ok (cast (x <: u64) <: u16)
        <:
        Core_models.Result.t_Result u16 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_41: t_TryFrom u32 u64 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: u64) -> true);
    f_try_from_post
    =
    (fun (x: u64) (out: Core_models.Result.t_Result u32 Core_models.Num.Error.t_TryFromIntError) ->
        true);
    f_try_from
    =
    fun (x: u64) ->
      if
        x >. (cast (Core_models.Num.impl_u32__MAX <: u32) <: u64) ||
        x <. (cast (Core_models.Num.impl_u32__MIN <: u32) <: u64)
      then
        Core_models.Result.Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        Core_models.Result.t_Result u32 Core_models.Num.Error.t_TryFromIntError
      else
        Core_models.Result.Result_Ok (cast (x <: u64) <: u32)
        <:
        Core_models.Result.t_Result u32 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_42: t_TryFrom usize u64 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: u64) -> true);
    f_try_from_post
    =
    (fun
        (x: u64)
        (out: Core_models.Result.t_Result usize Core_models.Num.Error.t_TryFromIntError)
        ->
        true);
    f_try_from
    =
    fun (x: u64) ->
      if
        x >. (cast (Core_models.Num.impl_usize__MAX <: usize) <: u64) ||
        x <. (cast (Core_models.Num.impl_usize__MIN <: usize) <: u64)
      then
        Core_models.Result.Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        Core_models.Result.t_Result usize Core_models.Num.Error.t_TryFromIntError
      else
        Core_models.Result.Result_Ok (cast (x <: u64) <: usize)
        <:
        Core_models.Result.t_Result usize Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_43: t_TryFrom u8 u128 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: u128) -> true);
    f_try_from_post
    =
    (fun (x: u128) (out: Core_models.Result.t_Result u8 Core_models.Num.Error.t_TryFromIntError) ->
        true);
    f_try_from
    =
    fun (x: u128) ->
      if
        x >. (cast (Core_models.Num.impl_u8__MAX <: u8) <: u128) ||
        x <. (cast (Core_models.Num.impl_u8__MIN <: u8) <: u128)
      then
        Core_models.Result.Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        Core_models.Result.t_Result u8 Core_models.Num.Error.t_TryFromIntError
      else
        Core_models.Result.Result_Ok (cast (x <: u128) <: u8)
        <:
        Core_models.Result.t_Result u8 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_44: t_TryFrom u16 u128 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: u128) -> true);
    f_try_from_post
    =
    (fun (x: u128) (out: Core_models.Result.t_Result u16 Core_models.Num.Error.t_TryFromIntError) ->
        true);
    f_try_from
    =
    fun (x: u128) ->
      if
        x >. (cast (Core_models.Num.impl_u16__MAX <: u16) <: u128) ||
        x <. (cast (Core_models.Num.impl_u16__MIN <: u16) <: u128)
      then
        Core_models.Result.Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        Core_models.Result.t_Result u16 Core_models.Num.Error.t_TryFromIntError
      else
        Core_models.Result.Result_Ok (cast (x <: u128) <: u16)
        <:
        Core_models.Result.t_Result u16 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_45: t_TryFrom u32 u128 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: u128) -> true);
    f_try_from_post
    =
    (fun (x: u128) (out: Core_models.Result.t_Result u32 Core_models.Num.Error.t_TryFromIntError) ->
        true);
    f_try_from
    =
    fun (x: u128) ->
      if
        x >. (cast (Core_models.Num.impl_u32__MAX <: u32) <: u128) ||
        x <. (cast (Core_models.Num.impl_u32__MIN <: u32) <: u128)
      then
        Core_models.Result.Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        Core_models.Result.t_Result u32 Core_models.Num.Error.t_TryFromIntError
      else
        Core_models.Result.Result_Ok (cast (x <: u128) <: u32)
        <:
        Core_models.Result.t_Result u32 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_46: t_TryFrom u64 u128 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: u128) -> true);
    f_try_from_post
    =
    (fun (x: u128) (out: Core_models.Result.t_Result u64 Core_models.Num.Error.t_TryFromIntError) ->
        true);
    f_try_from
    =
    fun (x: u128) ->
      if
        x >. (cast (Core_models.Num.impl_u64__MAX <: u64) <: u128) ||
        x <. (cast (Core_models.Num.impl_u64__MIN <: u64) <: u128)
      then
        Core_models.Result.Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        Core_models.Result.t_Result u64 Core_models.Num.Error.t_TryFromIntError
      else
        Core_models.Result.Result_Ok (cast (x <: u128) <: u64)
        <:
        Core_models.Result.t_Result u64 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_47: t_TryFrom usize u128 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: u128) -> true);
    f_try_from_post
    =
    (fun
        (x: u128)
        (out: Core_models.Result.t_Result usize Core_models.Num.Error.t_TryFromIntError)
        ->
        true);
    f_try_from
    =
    fun (x: u128) ->
      if
        x >. (cast (Core_models.Num.impl_usize__MAX <: usize) <: u128) ||
        x <. (cast (Core_models.Num.impl_usize__MIN <: usize) <: u128)
      then
        Core_models.Result.Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        Core_models.Result.t_Result usize Core_models.Num.Error.t_TryFromIntError
      else
        Core_models.Result.Result_Ok (cast (x <: u128) <: usize)
        <:
        Core_models.Result.t_Result usize Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_48: t_TryFrom u8 usize =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: usize) -> true);
    f_try_from_post
    =
    (fun (x: usize) (out: Core_models.Result.t_Result u8 Core_models.Num.Error.t_TryFromIntError) ->
        true);
    f_try_from
    =
    fun (x: usize) ->
      if
        x >. (cast (Core_models.Num.impl_u8__MAX <: u8) <: usize) ||
        x <. (cast (Core_models.Num.impl_u8__MIN <: u8) <: usize)
      then
        Core_models.Result.Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        Core_models.Result.t_Result u8 Core_models.Num.Error.t_TryFromIntError
      else
        Core_models.Result.Result_Ok (cast (x <: usize) <: u8)
        <:
        Core_models.Result.t_Result u8 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_49: t_TryFrom u16 usize =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: usize) -> true);
    f_try_from_post
    =
    (fun
        (x: usize)
        (out: Core_models.Result.t_Result u16 Core_models.Num.Error.t_TryFromIntError)
        ->
        true);
    f_try_from
    =
    fun (x: usize) ->
      if
        x >. (cast (Core_models.Num.impl_u16__MAX <: u16) <: usize) ||
        x <. (cast (Core_models.Num.impl_u16__MIN <: u16) <: usize)
      then
        Core_models.Result.Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        Core_models.Result.t_Result u16 Core_models.Num.Error.t_TryFromIntError
      else
        Core_models.Result.Result_Ok (cast (x <: usize) <: u16)
        <:
        Core_models.Result.t_Result u16 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_50: t_TryFrom u32 usize =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: usize) -> true);
    f_try_from_post
    =
    (fun
        (x: usize)
        (out: Core_models.Result.t_Result u32 Core_models.Num.Error.t_TryFromIntError)
        ->
        true);
    f_try_from
    =
    fun (x: usize) ->
      if
        x >. (cast (Core_models.Num.impl_u32__MAX <: u32) <: usize) ||
        x <. (cast (Core_models.Num.impl_u32__MIN <: u32) <: usize)
      then
        Core_models.Result.Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        Core_models.Result.t_Result u32 Core_models.Num.Error.t_TryFromIntError
      else
        Core_models.Result.Result_Ok (cast (x <: usize) <: u32)
        <:
        Core_models.Result.t_Result u32 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_51: t_TryFrom i8 i16 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i16) -> true);
    f_try_from_post
    =
    (fun (x: i16) (out: Core_models.Result.t_Result i8 Core_models.Num.Error.t_TryFromIntError) ->
        true);
    f_try_from
    =
    fun (x: i16) ->
      if
        x >. (cast (Core_models.Num.impl_i8__MAX <: i8) <: i16) ||
        x <. (cast (Core_models.Num.impl_i8__MIN <: i8) <: i16)
      then
        Core_models.Result.Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        Core_models.Result.t_Result i8 Core_models.Num.Error.t_TryFromIntError
      else
        Core_models.Result.Result_Ok (cast (x <: i16) <: i8)
        <:
        Core_models.Result.t_Result i8 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_52: t_TryFrom i8 i32 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i32) -> true);
    f_try_from_post
    =
    (fun (x: i32) (out: Core_models.Result.t_Result i8 Core_models.Num.Error.t_TryFromIntError) ->
        true);
    f_try_from
    =
    fun (x: i32) ->
      if
        x >. (cast (Core_models.Num.impl_i8__MAX <: i8) <: i32) ||
        x <. (cast (Core_models.Num.impl_i8__MIN <: i8) <: i32)
      then
        Core_models.Result.Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        Core_models.Result.t_Result i8 Core_models.Num.Error.t_TryFromIntError
      else
        Core_models.Result.Result_Ok (cast (x <: i32) <: i8)
        <:
        Core_models.Result.t_Result i8 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_53: t_TryFrom i16 i32 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i32) -> true);
    f_try_from_post
    =
    (fun (x: i32) (out: Core_models.Result.t_Result i16 Core_models.Num.Error.t_TryFromIntError) ->
        true);
    f_try_from
    =
    fun (x: i32) ->
      if
        x >. (cast (Core_models.Num.impl_i16__MAX <: i16) <: i32) ||
        x <. (cast (Core_models.Num.impl_i16__MIN <: i16) <: i32)
      then
        Core_models.Result.Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        Core_models.Result.t_Result i16 Core_models.Num.Error.t_TryFromIntError
      else
        Core_models.Result.Result_Ok (cast (x <: i32) <: i16)
        <:
        Core_models.Result.t_Result i16 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_54: t_TryFrom i8 i64 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i64) -> true);
    f_try_from_post
    =
    (fun (x: i64) (out: Core_models.Result.t_Result i8 Core_models.Num.Error.t_TryFromIntError) ->
        true);
    f_try_from
    =
    fun (x: i64) ->
      if
        x >. (cast (Core_models.Num.impl_i8__MAX <: i8) <: i64) ||
        x <. (cast (Core_models.Num.impl_i8__MIN <: i8) <: i64)
      then
        Core_models.Result.Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        Core_models.Result.t_Result i8 Core_models.Num.Error.t_TryFromIntError
      else
        Core_models.Result.Result_Ok (cast (x <: i64) <: i8)
        <:
        Core_models.Result.t_Result i8 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_55: t_TryFrom i16 i64 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i64) -> true);
    f_try_from_post
    =
    (fun (x: i64) (out: Core_models.Result.t_Result i16 Core_models.Num.Error.t_TryFromIntError) ->
        true);
    f_try_from
    =
    fun (x: i64) ->
      if
        x >. (cast (Core_models.Num.impl_i16__MAX <: i16) <: i64) ||
        x <. (cast (Core_models.Num.impl_i16__MIN <: i16) <: i64)
      then
        Core_models.Result.Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        Core_models.Result.t_Result i16 Core_models.Num.Error.t_TryFromIntError
      else
        Core_models.Result.Result_Ok (cast (x <: i64) <: i16)
        <:
        Core_models.Result.t_Result i16 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_56: t_TryFrom i32 i64 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i64) -> true);
    f_try_from_post
    =
    (fun (x: i64) (out: Core_models.Result.t_Result i32 Core_models.Num.Error.t_TryFromIntError) ->
        true);
    f_try_from
    =
    fun (x: i64) ->
      if
        x >. (cast (Core_models.Num.impl_i32__MAX <: i32) <: i64) ||
        x <. (cast (Core_models.Num.impl_i32__MIN <: i32) <: i64)
      then
        Core_models.Result.Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        Core_models.Result.t_Result i32 Core_models.Num.Error.t_TryFromIntError
      else
        Core_models.Result.Result_Ok (cast (x <: i64) <: i32)
        <:
        Core_models.Result.t_Result i32 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_57: t_TryFrom isize i64 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i64) -> true);
    f_try_from_post
    =
    (fun
        (x: i64)
        (out: Core_models.Result.t_Result isize Core_models.Num.Error.t_TryFromIntError)
        ->
        true);
    f_try_from
    =
    fun (x: i64) ->
      if
        x >. (cast (Core_models.Num.impl_isize__MAX <: isize) <: i64) ||
        x <. (cast (Core_models.Num.impl_isize__MIN <: isize) <: i64)
      then
        Core_models.Result.Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        Core_models.Result.t_Result isize Core_models.Num.Error.t_TryFromIntError
      else
        Core_models.Result.Result_Ok (cast (x <: i64) <: isize)
        <:
        Core_models.Result.t_Result isize Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_58: t_TryFrom i8 i128 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i128) -> true);
    f_try_from_post
    =
    (fun (x: i128) (out: Core_models.Result.t_Result i8 Core_models.Num.Error.t_TryFromIntError) ->
        true);
    f_try_from
    =
    fun (x: i128) ->
      if
        x >. (cast (Core_models.Num.impl_i8__MAX <: i8) <: i128) ||
        x <. (cast (Core_models.Num.impl_i8__MIN <: i8) <: i128)
      then
        Core_models.Result.Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        Core_models.Result.t_Result i8 Core_models.Num.Error.t_TryFromIntError
      else
        Core_models.Result.Result_Ok (cast (x <: i128) <: i8)
        <:
        Core_models.Result.t_Result i8 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_59: t_TryFrom i16 i128 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i128) -> true);
    f_try_from_post
    =
    (fun (x: i128) (out: Core_models.Result.t_Result i16 Core_models.Num.Error.t_TryFromIntError) ->
        true);
    f_try_from
    =
    fun (x: i128) ->
      if
        x >. (cast (Core_models.Num.impl_i16__MAX <: i16) <: i128) ||
        x <. (cast (Core_models.Num.impl_i16__MIN <: i16) <: i128)
      then
        Core_models.Result.Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        Core_models.Result.t_Result i16 Core_models.Num.Error.t_TryFromIntError
      else
        Core_models.Result.Result_Ok (cast (x <: i128) <: i16)
        <:
        Core_models.Result.t_Result i16 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_60: t_TryFrom i32 i128 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i128) -> true);
    f_try_from_post
    =
    (fun (x: i128) (out: Core_models.Result.t_Result i32 Core_models.Num.Error.t_TryFromIntError) ->
        true);
    f_try_from
    =
    fun (x: i128) ->
      if
        x >. (cast (Core_models.Num.impl_i32__MAX <: i32) <: i128) ||
        x <. (cast (Core_models.Num.impl_i32__MIN <: i32) <: i128)
      then
        Core_models.Result.Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        Core_models.Result.t_Result i32 Core_models.Num.Error.t_TryFromIntError
      else
        Core_models.Result.Result_Ok (cast (x <: i128) <: i32)
        <:
        Core_models.Result.t_Result i32 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_61: t_TryFrom i64 i128 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i128) -> true);
    f_try_from_post
    =
    (fun (x: i128) (out: Core_models.Result.t_Result i64 Core_models.Num.Error.t_TryFromIntError) ->
        true);
    f_try_from
    =
    fun (x: i128) ->
      if
        x >. (cast (Core_models.Num.impl_i64__MAX <: i64) <: i128) ||
        x <. (cast (Core_models.Num.impl_i64__MIN <: i64) <: i128)
      then
        Core_models.Result.Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        Core_models.Result.t_Result i64 Core_models.Num.Error.t_TryFromIntError
      else
        Core_models.Result.Result_Ok (cast (x <: i128) <: i64)
        <:
        Core_models.Result.t_Result i64 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_62: t_TryFrom isize i128 =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: i128) -> true);
    f_try_from_post
    =
    (fun
        (x: i128)
        (out: Core_models.Result.t_Result isize Core_models.Num.Error.t_TryFromIntError)
        ->
        true);
    f_try_from
    =
    fun (x: i128) ->
      if
        x >. (cast (Core_models.Num.impl_isize__MAX <: isize) <: i128) ||
        x <. (cast (Core_models.Num.impl_isize__MIN <: isize) <: i128)
      then
        Core_models.Result.Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        Core_models.Result.t_Result isize Core_models.Num.Error.t_TryFromIntError
      else
        Core_models.Result.Result_Ok (cast (x <: i128) <: isize)
        <:
        Core_models.Result.t_Result isize Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_63: t_TryFrom i8 isize =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: isize) -> true);
    f_try_from_post
    =
    (fun (x: isize) (out: Core_models.Result.t_Result i8 Core_models.Num.Error.t_TryFromIntError) ->
        true);
    f_try_from
    =
    fun (x: isize) ->
      if
        x >. (cast (Core_models.Num.impl_i8__MAX <: i8) <: isize) ||
        x <. (cast (Core_models.Num.impl_i8__MIN <: i8) <: isize)
      then
        Core_models.Result.Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        Core_models.Result.t_Result i8 Core_models.Num.Error.t_TryFromIntError
      else
        Core_models.Result.Result_Ok (cast (x <: isize) <: i8)
        <:
        Core_models.Result.t_Result i8 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_64: t_TryFrom i16 isize =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: isize) -> true);
    f_try_from_post
    =
    (fun
        (x: isize)
        (out: Core_models.Result.t_Result i16 Core_models.Num.Error.t_TryFromIntError)
        ->
        true);
    f_try_from
    =
    fun (x: isize) ->
      if
        x >. (cast (Core_models.Num.impl_i16__MAX <: i16) <: isize) ||
        x <. (cast (Core_models.Num.impl_i16__MIN <: i16) <: isize)
      then
        Core_models.Result.Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        Core_models.Result.t_Result i16 Core_models.Num.Error.t_TryFromIntError
      else
        Core_models.Result.Result_Ok (cast (x <: isize) <: i16)
        <:
        Core_models.Result.t_Result i16 Core_models.Num.Error.t_TryFromIntError
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_65: t_TryFrom i32 isize =
  {
    f_Error = Core_models.Num.Error.t_TryFromIntError;
    f_try_from_pre = (fun (x: isize) -> true);
    f_try_from_post
    =
    (fun
        (x: isize)
        (out: Core_models.Result.t_Result i32 Core_models.Num.Error.t_TryFromIntError)
        ->
        true);
    f_try_from
    =
    fun (x: isize) ->
      if
        x >. (cast (Core_models.Num.impl_i32__MAX <: i32) <: isize) ||
        x <. (cast (Core_models.Num.impl_i32__MIN <: i32) <: isize)
      then
        Core_models.Result.Result_Err
        (Core_models.Num.Error.TryFromIntError (() <: Prims.unit)
          <:
          Core_models.Num.Error.t_TryFromIntError)
        <:
        Core_models.Result.t_Result i32 Core_models.Num.Error.t_TryFromIntError
      else
        Core_models.Result.Result_Ok (cast (x <: isize) <: i32)
        <:
        Core_models.Result.t_Result i32 Core_models.Num.Error.t_TryFromIntError
  }
