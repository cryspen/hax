module Tests.Legacy__side_effects.Issue_1299_
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_Foo = { f_y:u8 }

type t_S = { f_g:t_Foo }

type t_OtherS = { f_g:Core_models.Option.t_Option t_Foo }

let impl_Foo__from (i: t_Foo) : t_Foo =
  { f_y = Core_models.Clone.f_clone #u8 #FStar.Tactics.Typeclasses.solve i.f_y } <: t_Foo

type t_Error = | Error : t_Error

let impl_S__from (i: t_OtherS) : Core_models.Result.t_Result t_S t_Error =
  match
    Core_models.Option.impl__ok_or #t_Foo
      #t_Error
      (Core_models.Option.impl__as_ref #t_Foo i.f_g <: Core_models.Option.t_Option t_Foo)
      (Error <: t_Error)
    <:
    Core_models.Result.t_Result t_Foo t_Error
  with
  | Core_models.Result.Result_Ok hoist47 ->
    Core_models.Result.Result_Ok ({ f_g = impl_Foo__from hoist47 } <: t_S)
    <:
    Core_models.Result.t_Result t_S t_Error
  | Core_models.Result.Result_Err err ->
    Core_models.Result.Result_Err err <: Core_models.Result.t_Result t_S t_Error
