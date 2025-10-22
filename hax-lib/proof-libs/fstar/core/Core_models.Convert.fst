
module Core_models.Convert
open Rust_primitives

class t_TryInto self t = {
  [@@@FStar.Tactics.Typeclasses.no_method]
  f_Error: Type0;
  f_try_into: self -> Core_models.Result.t_Result t f_Error
}

instance impl_6 (t: Type0) (len: usize): t_TryInto (t_Slice t) (t_Array t len) = {
  f_Error = Core_models.Array.t_TryFromSliceError;
  f_try_into = (fun (s: t_Slice t) -> 
    if Core_models.Slice.impl__len s = len
    then Core_models.Result.Result_Ok (s <: t_Array t len)
    else Core_models.Result.Result_Err Core_models.Array.TryFromSliceError
  )
}

instance impl_6_refined (t: Type0) (len: usize): t_TryInto (s: t_Slice t {Core_models.Slice.impl__len s == len}) (t_Array t len) = {
  f_Error = Core_models.Array.t_TryFromSliceError;
  f_try_into = (fun (s: t_Slice t {Core_models.Slice.impl__len s == len}) -> 
    Core_models.Result.Result_Ok (s <: t_Array t len)
  )
}

class t_Into self t = {
  f_into_pre: self -> bool;
  f_into_post: self -> t -> bool;
  f_into: self -> t;
}

class t_From self t = {
  f_from_pre: t -> bool;
  f_from_post: t -> self -> bool;
  f_from: t -> self;
}

class t_TryFrom self t = {
  [@@@FStar.Tactics.Typeclasses.no_method]
  f_Error: Type0;
  f_try_from_pre: t -> bool;
  f_try_from_post: t -> Core_models.Result.t_Result self f_Error -> bool;
  f_try_from: t -> Core_models.Result.t_Result self f_Error;
}

instance integer_into
  (t:inttype) (t':inttype { minint t >= minint t' /\ maxint t <= maxint t' })
  : t_From (int_t t') (int_t t)
  = {
      f_from_pre = (fun _ -> true);
      f_from_post = (fun _ _ -> true);
      f_from = (fun (x: int_t t) -> Rust_primitives.Integers.cast #t #t' x);
    }

instance into_from_from a b {| t_From a b |}: t_Into b a = {
  f_into_pre = (fun _ -> true);
  f_into_post = (fun _ _ -> true);
  f_into = (fun x -> f_from x)
}

type t_Infallible = _:unit{False}

instance try_from_from_from a b {| t_From a b |}: t_TryFrom a b = {
  f_Error = t_Infallible;
  f_try_from_pre = (fun _ -> true);
  f_try_from_post = (fun _ _ -> true);
  f_try_from = (fun x -> Core_models.Result.Result_Ok (f_from x))
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let try_into_from_try_from a b {| i1: t_TryFrom a b |}: t_TryInto b a = {
  f_Error = i1.f_Error;
  f_try_into = (fun x -> f_try_from x)
}

instance integer_try_into_u32_usize : t_TryInto u32 usize = {
  f_Error = Core_models.Num.Error.t_TryFromIntError;
  f_try_into = (fun (x: u32) ->
    if range (v #U32 x) USIZE
    then Core_models.Result.Result_Ok (Rust_primitives.Integers.cast #U32 #USIZE x)
    else Core_models.Result.Result_Err (Core_models.Num.Error.TryFromIntError ())
  )
}

instance integer_try_into_u32_u16: t_TryInto u32 u16 = {
  f_Error = Core.Num.Error.t_TryFromIntError;
  f_try_into = (fun (x: u32) ->
    if range (v #U32 x) U16
    then Core.Result.Result_Ok (Rust_primitives.Integers.cast #U32 #U16 x)
    else Core.Result.Result_Err ()
  )
}

instance integer_try_into_u64_u32: t_TryInto u64 u32 = {
  f_Error = Core.Num.Error.t_TryFromIntError;
  f_try_into = (fun (x: u64) ->
    if range (v #U64 x) U32
    then Core.Result.Result_Ok (Rust_primitives.Integers.cast #U64 #U32 x)
    else Core.Result.Result_Err ()
  )
}

instance integer_try_from_u8_usize : t_TryFrom u8 usize = {
  f_Error = Core_models.Num.Error.t_TryFromIntError;
  f_try_from = (fun (x: usize) ->
    if range (v #USIZE x) U8
    then Core_models.Result.Result_Ok (Rust_primitives.Integers.cast #USIZE #U8 x)
    else Core_models.Result.Result_Err (Core_models.Num.Error.TryFromIntError ())
  );
  f_try_from_pre = (fun _ -> true);
  f_try_from_post = (fun _ _ -> true);
}

instance integer_try_from_u16_usize : t_TryFrom u16 usize = {
  f_Error = Core_models.Num.Error.t_TryFromIntError;
  f_try_from = (fun (x: usize) ->
    if range (v #USIZE x) U16
    then Core_models.Result.Result_Ok (Rust_primitives.Integers.cast #USIZE #U16 x)
    else Core_models.Result.Result_Err (Core_models.Num.Error.TryFromIntError ())
  );
  f_try_from_pre = (fun _ -> true);
  f_try_from_post = (fun _ _ -> true);
}

instance integer_try_into_usize_u64 : t_TryInto usize u64 = {
  f_Error = Core_models.Num.Error.t_TryFromIntError;
  f_try_into = (fun (x: usize) ->
    Core_models.Result.Result_Ok (Rust_primitives.Integers.cast #USIZE #U64 x)
  )
}

instance integer_try_into_infallible (t:inttype) (t':inttype) {|included t t'|} : t_TryInto (int_t t) (int_t t') = {
  f_Error = t_Infallible;
  f_try_into = (fun (x: int_t t) ->
    Core_models.Result.Result_Ok (Rust_primitives.Integers.cast #t #t' x)
  )
}

instance integer_try_into (t:inttype) (t':inttype) {|~ (included t t')|} : t_TryInto (int_t t) (int_t t') = {
  f_Error = Core_models.Num.Error.t_TryFromIntError;
  f_try_into = (fun (x: int_t t) ->
    if range (v #t x) t'
    then Core_models.Result.Result_Ok (Rust_primitives.Integers.cast #t #t' x)
    else Core_models.Result.Result_Err (Core_models.Num.Error.TryFromIntError ())
  )
}

instance from_id a: t_From a a = {
  f_from_pre = (fun _ -> true);
  f_from_post = (fun _ _ -> true);
  f_from = (fun x -> x)
}

class t_AsRef self t = {
  f_as_ref_pre: self -> bool;
  f_as_ref_post: self -> t -> bool;
  f_as_ref: self -> t;
}

instance as_ref_id a: t_AsRef a a = {
  f_as_ref_pre = (fun _ -> true);
  f_as_ref_post = (fun _ _ -> true);
  f_as_ref = (fun x -> x)
}
