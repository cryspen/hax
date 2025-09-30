module Tests.Rustc_tests__generic_unused_impl
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_W (v_T: Type0) = | W : v_T -> t_W v_T

let main (_: Prims.unit) : Prims.unit = ()

class t_Foo (v_Self: Type0) = {
  f_Assoc:Type0;
  f_from_pre:f_Assoc -> Type0;
  f_from_post:f_Assoc -> v_Self -> Type0;
  f_from:x0: f_Assoc -> Prims.Pure v_Self (f_from_pre x0) (fun result -> f_from_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Foo v_T)
    : Core.Convert.t_From (t_W v_T) (t_Array i0.f_Assoc (mk_usize 1)) =
  {
    f_from_pre = (fun (from: t_Array i0.f_Assoc (mk_usize 1)) -> true);
    f_from_post = (fun (from: t_Array i0.f_Assoc (mk_usize 1)) (out: t_W v_T) -> true);
    f_from
    =
    fun (from: t_Array i0.f_Assoc (mk_usize 1)) ->
      Rust_primitives.Hax.failure "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/804.\nPlease upvote or comment this issue if you see this error message.\nPat:Array\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/804.\nPlease upvote or comment this issue if you see this error message.[90m\nNote: the error was labeled with context `AST import`.\n[0m"
        ""
  }
