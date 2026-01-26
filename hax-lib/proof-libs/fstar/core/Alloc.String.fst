module Alloc.String
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

type t_String = | String : string -> t_String

let impl_String__new (_: Prims.unit) : t_String = String "" <: t_String

let impl_String__push_str (self: t_String) (other: string) : t_String =
  let self:t_String = String (Rust_primitives.String.str_concat self._0 other) <: t_String in
  self

let impl_String__push (self: t_String) (c: FStar.Char.char) : t_String =
  let self:t_String =
    String
    (Rust_primitives.String.str_concat self._0 (Rust_primitives.String.str_of_char c <: string))
    <:
    t_String
  in
  self

let impl_String__pop (self: t_String) : (t_String & Core_models.Option.t_Option FStar.Char.char) =
  let l:usize = Core_models.Str.impl_str__len self._0 in
  let (self: t_String), (hax_temp_output: Core_models.Option.t_Option FStar.Char.char) =
    if l >. mk_usize 0
    then
      let self:t_String =
        String (Rust_primitives.String.str_sub self._0 (mk_usize 0) (l -! mk_usize 1 <: usize))
        <:
        t_String
      in
      self,
      (Core_models.Option.Option_Some
        (Rust_primitives.String.str_index self._0 (l -! mk_usize 1 <: usize))
        <:
        Core_models.Option.t_Option FStar.Char.char)
      <:
      (t_String & Core_models.Option.t_Option FStar.Char.char)
    else
      self, (Core_models.Option.Option_None <: Core_models.Option.t_Option FStar.Char.char)
      <:
      (t_String & Core_models.Option.t_Option FStar.Char.char)
  in
  self, hax_temp_output <: (t_String & Core_models.Option.t_Option FStar.Char.char)
