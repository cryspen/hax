module New_tests.Legacy__dyn__lib
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

class t_Printable (v_Self: Type0) (v_S: Type0) = {
  f_stringify_pre:v_Self -> Type0;
  f_stringify_post:v_Self -> v_S -> Type0;
  f_stringify:x0: v_Self
    -> Prims.Pure v_S (f_stringify_pre x0) (fun result -> f_stringify_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_Printable i32 Alloc.String.t_String =
  {
    f_stringify_pre = (fun (self: i32) -> true);
    f_stringify_post = (fun (self: i32) (out: Alloc.String.t_String) -> true);
    f_stringify
    =
    fun (self: i32) -> Alloc.String.f_to_string #i32 #FStar.Tactics.Typeclasses.solve self
  }

(* [hax::excluded] print — Explicit rejection by a phase in the Hax engine: a node of kind [Dyn] have been found in the AST *)
