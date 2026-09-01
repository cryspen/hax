module Alloc.String
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::string::String`]. The model is a plain string value; there is
/// no separate buffer, so "capacity" is always exactly the length (see
/// [`String::capacity`]).
type t_String = | String : string -> t_String

/// See [`std::string::FromUtf8Error`]: carries back the bytes that failed
/// to decode.
/// DEVIATION(std): no `utf8_error()`. It returns a `core::str::Utf8Error`,
/// and the model's `Utf8Error` is a contentless placeholder with no way to
/// build a value, so the accessor cannot be provided honestly.
type t_FromUtf8Error = | FromUtf8Error : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global -> t_FromUtf8Error

/// See [`std::string::ToString`].
/// In real core `to_string` is a required method of `ToString` and the
/// trait is blanket-implemented over `Display`; the model mirrors both.
class t_ToString (v_Self: Type0) = {
  f_to_string_pre:v_Self -> Type0;
  f_to_string_post:v_Self -> t_String -> Type0;
  f_to_string:x0: v_Self
    -> Prims.Pure t_String (f_to_string_pre x0) (fun result -> f_to_string_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': #v_T: Type0 -> {| i0: Core_models.Fmt.t_Display v_T |} -> t_ToString v_T

unfold
let impl_1
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Fmt.t_Display v_T)
     = impl_1' #v_T #i0

/// See [`std::string::String::new`]
let impl_String__new (_: Prims.unit) : t_String = String "" <: t_String

/// See [`std::string::String::with_capacity`]: the requested capacity
/// is irrelevant to the model (see [`String::capacity`]).
let impl_String__with_capacity (e_capacity: usize) : t_String = String "" <: t_String

/// See `std::string::String::try_with_capacity` (unstable). The model
/// never fails to allocate.
let impl_String__try_with_capacity (e_capacity: usize)
    : Core_models.Result.t_Result t_String Alloc.Collections.t_TryReserveError =
  Core_models.Result.Result_Ok (String "" <: t_String)
  <:
  Core_models.Result.t_Result t_String Alloc.Collections.t_TryReserveError

/// See [`std::string::String::from_utf8`]
let impl_String__from_utf8 (vec: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
    : Core_models.Result.t_Result t_String t_FromUtf8Error =
  if
    Rust_primitives.String.str_is_utf8 (Alloc.Vec.impl_1__as_slice #u8 #Alloc.Alloc.t_Global vec
        <:
        t_Slice u8)
  then
    Core_models.Result.Result_Ok
    (String
      (Rust_primitives.String.str_from_utf8_lossy (Alloc.Vec.impl_1__as_slice #u8
              #Alloc.Alloc.t_Global
              vec
            <:
            t_Slice u8))
      <:
      t_String)
    <:
    Core_models.Result.t_Result t_String t_FromUtf8Error
  else
    Core_models.Result.Result_Err (FromUtf8Error vec <: t_FromUtf8Error)
    <:
    Core_models.Result.t_Result t_String t_FromUtf8Error

/// See [`std::string::String::from_utf8_lossy`].
/// DEVIATION(std): returns a `String` rather than a `Cow<\'_, str>`. The
/// model\'s `Cow<T>` is sized-only, so `Cow<\'_, str>` is not statable.
let impl_String__from_utf8_lossy (v: t_Slice u8) : t_String =
  String (Rust_primitives.String.str_from_utf8_lossy v) <: t_String

/// See `std::string::String::from_utf8_lossy_owned` (unstable).
let impl_String__from_utf8_lossy_owned (v: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) : t_String =
  String
  (Rust_primitives.String.str_from_utf8_lossy (Alloc.Vec.impl_1__as_slice #u8
          #Alloc.Alloc.t_Global
          v
        <:
        t_Slice u8))
  <:
  t_String

/// See [`std::string::String::push_str`]
let impl_String__push_str (self: t_String) (other: string) : t_String =
  let self:t_String = String (Rust_primitives.String.str_concat self._0 other) <: t_String in
  self

/// See [`std::string::String::push`]
let impl_String__push (self: t_String) (c: FStar.Char.char) : t_String =
  let self:t_String =
    String
    (Rust_primitives.String.str_concat self._0 (Rust_primitives.String.str_of_char c <: string))
    <:
    t_String
  in
  self

/// See [`std::string::String::pop`]
let impl_String__pop (self: t_String) : (t_String & Core_models.Option.t_Option FStar.Char.char) =
  let l:usize = Rust_primitives.String.str_len self._0 in
  let (self: t_String), (hax_temp_output: Core_models.Option.t_Option FStar.Char.char) =
    if l >. mk_usize 0
    then
      let c:FStar.Char.char = Rust_primitives.String.str_index self._0 (l -! mk_usize 1 <: usize) in
      let self:t_String =
        String (Rust_primitives.String.str_sub self._0 (mk_usize 0) (l -! mk_usize 1 <: usize))
        <:
        t_String
      in
      self, (Core_models.Option.Option_Some c <: Core_models.Option.t_Option FStar.Char.char)
      <:
      (t_String & Core_models.Option.t_Option FStar.Char.char)
    else
      self, (Core_models.Option.Option_None <: Core_models.Option.t_Option FStar.Char.char)
      <:
      (t_String & Core_models.Option.t_Option FStar.Char.char)
  in
  self, hax_temp_output <: (t_String & Core_models.Option.t_Option FStar.Char.char)

/// See [`std::string::String::len`]: the length in **bytes**.
let impl_String__len (self: t_String) : usize = Core_models.Str.impl_str__len self._0

/// See [`std::string::String::is_empty`]
let impl_String__is_empty (self: t_String) : bool =
  (Core_models.Str.impl_str__len self._0 <: usize) =. mk_usize 0

/// See [`std::string::String::as_str`]
let impl_String__as_str (self: t_String) : string = self._0

/// See [`std::string::String::as_bytes`]
let impl_String__as_bytes (self: t_String) : t_Slice u8 = Core_models.Str.impl_str__as_bytes self._0

/// See [`std::string::String::into_bytes`]
let impl_String__into_bytes (self: t_String) : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  let seq:Rust_primitives.Sequence.t_Seq u8 = Rust_primitives.Sequence.seq_empty #u8 () in
  let seq:Rust_primitives.Sequence.t_Seq u8 =
    Rust_primitives.Sequence.seq_extend #u8
      seq
      (Core_models.Str.impl_str__as_bytes self._0 <: t_Slice u8)
  in
  Alloc.Vec.from_seq #u8 #Alloc.Alloc.t_Global seq

/// See [`std::string::String::into_boxed_str`]
let impl_String__into_boxed_str (self: t_String) : string =
  Core_models.Convert.f_from #string #string #FStar.Tactics.Typeclasses.solve self._0

/// See [`std::string::String::clear`]
let impl_String__clear (self: t_String) : t_String =
  let self:t_String = String "" <: t_String in
  self

/// See [`std::string::String::retain`].
/// Opaque: the body below is the real filter, and `cargo test` checks it
/// against std, but it does not survive extraction — the model\'s `Fn*`
/// traits carry `Output` as a non-method field, so F* cannot see that
/// `f(c)` is a `bool` and rejects the `if`.
assume
val impl_String__retain':
    #v_F: Type0 ->
    {| i0: Core_models.Ops.Function.t_FnMut v_F FStar.Char.char |} ->
    self: t_String ->
    f: v_F
  -> t_String

unfold
let impl_String__retain
      (#v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Core_models.Ops.Function.t_FnMut v_F FStar.Char.char)
     = impl_String__retain' #v_F #i0

/// See [`std::string::String::capacity`].
/// DEVIATION(std): the model holds a string value, not a buffer, so the
/// capacity is always exactly the length. std only guarantees
/// `capacity() >= len()`, which this respects, but the concrete numbers
/// it reports differ.
let impl_String__capacity (self: t_String) : usize = Core_models.Str.impl_str__len self._0

/// See [`std::string::String::reserve`]: a no-op, as the model has no
/// buffer to grow.
let impl_String__reserve (self: t_String) (e_additional: usize) : t_String = self

/// See [`std::string::String::reserve_exact`]: a no-op, as
/// [`String::reserve`].
let impl_String__reserve_exact (self: t_String) (e_additional: usize) : t_String = self

/// See [`std::string::String::try_reserve`]: the model never fails to
/// allocate.
let impl_String__try_reserve (self: t_String) (e_additional: usize)
    : (t_String & Core_models.Result.t_Result Prims.unit Alloc.Collections.t_TryReserveError) =
  let hax_temp_output:Core_models.Result.t_Result Prims.unit Alloc.Collections.t_TryReserveError =
    Core_models.Result.Result_Ok (() <: Prims.unit)
    <:
    Core_models.Result.t_Result Prims.unit Alloc.Collections.t_TryReserveError
  in
  self, hax_temp_output
  <:
  (t_String & Core_models.Result.t_Result Prims.unit Alloc.Collections.t_TryReserveError)

/// See [`std::string::String::try_reserve_exact`]: as
/// [`String::try_reserve`].
let impl_String__try_reserve_exact (self: t_String) (e_additional: usize)
    : (t_String & Core_models.Result.t_Result Prims.unit Alloc.Collections.t_TryReserveError) =
  let hax_temp_output:Core_models.Result.t_Result Prims.unit Alloc.Collections.t_TryReserveError =
    Core_models.Result.Result_Ok (() <: Prims.unit)
    <:
    Core_models.Result.t_Result Prims.unit Alloc.Collections.t_TryReserveError
  in
  self, hax_temp_output
  <:
  (t_String & Core_models.Result.t_Result Prims.unit Alloc.Collections.t_TryReserveError)

/// See [`std::string::String::shrink_to_fit`]: a no-op, as
/// [`String::reserve`].
let impl_String__shrink_to_fit (self: t_String) : t_String = self

/// See [`std::string::String::shrink_to`]: a no-op, as
/// [`String::reserve`].
let impl_String__shrink_to (self: t_String) (e_min_capacity: usize) : t_String = self

/// See [`std::string::String::truncate`]: `new_len` is a **byte**
/// index, and a `new_len` past the end is a no-op rather than a panic.
let impl_String__truncate (self: t_String) (new_len: usize)
    : Prims.Pure t_String
      (requires
        new_len >. (Core_models.Str.impl_str__len self._0 <: usize) ||
        Rust_primitives.String.str_is_char_boundary self._0 new_len)
      (fun _ -> Prims.l_True) =
  let self:t_String =
    if new_len <=. (Core_models.Str.impl_str__len self._0 <: usize)
    then String (Rust_primitives.String.str_sub_bytes self._0 (mk_usize 0) new_len) <: t_String
    else self
  in
  self

/// See [`std::string::String::split_off`]: `at` is a **byte** index.
let impl_String__split_off (self: t_String) (at: usize)
    : Prims.Pure (t_String & t_String)
      (requires Rust_primitives.String.str_is_char_boundary self._0 at)
      (fun _ -> Prims.l_True) =
  let l:usize = Core_models.Str.impl_str__len self._0 in
  let tail:t_String = String (Rust_primitives.String.str_sub_bytes self._0 at l) <: t_String in
  let self:t_String =
    String (Rust_primitives.String.str_sub_bytes self._0 (mk_usize 0) at) <: t_String
  in
  let hax_temp_output:t_String = tail in
  self, hax_temp_output <: (t_String & t_String)

/// See [`std::string::String::insert_str`]: `idx` is a **byte** index.
let impl_String__insert_str (self: t_String) (idx: usize) (v_string: string)
    : Prims.Pure t_String
      (requires Rust_primitives.String.str_is_char_boundary self._0 idx)
      (fun _ -> Prims.l_True) =
  let l:usize = Core_models.Str.impl_str__len self._0 in
  let self:t_String =
    String
    (Rust_primitives.String.str_concat (Rust_primitives.String.str_concat (Rust_primitives.String.str_sub_bytes
                self._0
                (mk_usize 0)
                idx
              <:
              string)
            v_string
          <:
          string)
        (Rust_primitives.String.str_sub_bytes self._0 idx l <: string))
    <:
    t_String
  in
  self

/// See [`std::string::String::insert`]: `idx` is a **byte** index, `ch`
/// is inserted in its UTF-8 encoding.
let impl_String__insert (self: t_String) (idx: usize) (ch: FStar.Char.char)
    : Prims.Pure t_String
      (requires Rust_primitives.String.str_is_char_boundary self._0 idx)
      (fun _ -> Prims.l_True) =
  let self:t_String =
    impl_String__insert_str self idx (Rust_primitives.String.str_of_char ch <: string)
  in
  self

/// See [`std::string::String::remove`]: `idx` is the **byte** index of
/// the char to remove.
let impl_String__remove (self: t_String) (idx: usize)
    : Prims.Pure (t_String & FStar.Char.char)
      (requires
        idx <. (Core_models.Str.impl_str__len self._0 <: usize) &&
        Rust_primitives.String.str_is_char_boundary self._0 idx)
      (fun _ -> Prims.l_True) =
  let l:usize = Core_models.Str.impl_str__len self._0 in
  let tail:string = Rust_primitives.String.str_sub_bytes self._0 idx l in
  let ch:FStar.Char.char = Rust_primitives.String.str_index tail (mk_usize 0) in
  let self:t_String =
    String
    (Rust_primitives.String.str_concat (Rust_primitives.String.str_sub_bytes self._0
            (mk_usize 0)
            idx
          <:
          string)
        (Rust_primitives.String.str_sub tail
            (mk_usize 1)
            (Rust_primitives.String.str_char_count tail <: usize)
          <:
          string))
    <:
    t_String
  in
  let hax_temp_output:FStar.Char.char = ch in
  self, hax_temp_output <: (t_String & FStar.Char.char)
