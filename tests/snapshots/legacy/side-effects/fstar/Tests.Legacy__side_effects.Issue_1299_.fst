module Tests.Legacy__side_effects.Issue_1299_
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_Foo = { f_y:u8 }

type t_S = { f_g:t_Foo }

type t_OtherS = { f_g:Core.Option.t_Option t_Foo }

let impl_Foo__from (i: t_Foo) : t_Foo =
  { f_y = Core.Clone.f_clone #u8 #FStar.Tactics.Typeclasses.solve i.f_y } <: t_Foo

type t_Error = | Error : t_Error

let impl_S__from (i: t_OtherS) : Core.Result.t_Result t_S t_Error =
  match
    Core.Option.impl__ok_or #t_Foo
      #t_Error
      (Core.Option.impl__as_ref #t_Foo i.f_g <: Core.Option.t_Option t_Foo)
      (Error <: t_Error)
    <:
    Core.Result.t_Result t_Foo t_Error
  with
  | Core.Result.Result_Ok hoist47 ->
    Core.Result.Result_Ok ({ f_g = impl_Foo__from hoist47 } <: t_S)
    <:
    Core.Result.t_Result t_S t_Error
  | Core.Result.Result_Err err -> Core.Result.Result_Err err <: Core.Result.t_Result t_S t_Error
