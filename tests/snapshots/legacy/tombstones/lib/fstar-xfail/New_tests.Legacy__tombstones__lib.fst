module New_tests.Legacy__tombstones__lib
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let clean_add (a b: u8) : u8 = a +! b

(* [hax::excluded] t_RawHolder — Explicit rejection by a phase in the Hax engine: a node of kind [Raw_pointer] have been found in the AST *)

class t_Speak (v_Self: Type0) = {
  f_hello_pre:v_Self -> Type0;
  f_hello_post:v_Self -> u8 -> Type0;
  f_hello:x0: v_Self -> Prims.Pure u8 (f_hello_pre x0) (fun result -> f_hello_post x0 result)
}

type t_Cat = | Cat : t_Cat

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_Speak t_Cat =
  {
    f_hello_pre = (fun (self: t_Cat) -> true);
    f_hello_post = (fun (self: t_Cat) (out: u8) -> true);
    f_hello = fun (self: t_Cat) -> mk_u8 1
  }

(* [hax::excluded] dyn_in_sig — Explicit rejection by a phase in the Hax engine: a node of kind [Dyn] have been found in the AST *)

/// @fail(extraction): coq(HAX0008, HAX0008, HAX0008), proverif(HAX0008, HAX0008, HAX0008), fstar(HAX0008, HAX0008, HAX0008), ssprove(HAX0008, HAX0008, HAX0008)
let dyn_in_body (_: Prims.unit) : u8 =
  let c:t_Cat = Cat <: t_Cat in
  Rust_primitives.Hax.failure "[hax::opaque] Explicit rejection by a phase in the Hax engine: a node of kind [Dyn] have been found in the AST"
    ""

(* [hax::excluded] mut_ref_return — something is not implemented yet. This function returns a mutable reference, which the backend cannot state; the item is excluded. *)

/// @fail(extraction): proverif(HAX0003, HAX0003, HAX0003, HAX0010, HAX0010, HAX0010), ssprove(HAX0003, HAX0003, HAX0003, HAX0010, HAX0010, HAX0010), coq(HAX0003, HAX0003, HAX0003, HAX0010, HAX0010, HAX0010)
assume
val body_split': buf: t_Slice u8 -> (t_Slice u8 & u8)

unfold
let body_split = body_split'
