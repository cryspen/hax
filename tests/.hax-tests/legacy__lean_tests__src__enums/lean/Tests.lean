
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

inductive Tests.Legacy__lean_tests__src__enums.E : Type
| V1 : Tests.Legacy__lean_tests__src__enums.E 
| V2 : Tests.Legacy__lean_tests__src__enums.E 
| V3 : usize -> Tests.Legacy__lean_tests__src__enums.E 
| V4 : usize -> usize -> usize -> Tests.Legacy__lean_tests__src__enums.E 
| V5 (f1 : usize) (f2 : usize) : Tests.Legacy__lean_tests__src__enums.E 
| V6 (f1 : usize) (f2 : usize) : Tests.Legacy__lean_tests__src__enums.E 


inductive Tests.Legacy__lean_tests__src__enums.MyList (T : Type) : Type
| Nil : Tests.Legacy__lean_tests__src__enums.MyList (T : Type) 
| Cons (hd : T)
       (tl : (Alloc.Boxed.Box
         (Tests.Legacy__lean_tests__src__enums.MyList T)
         Alloc.Alloc.Global))
    : Tests.Legacy__lean_tests__src__enums.MyList (T : Type) 


def Tests.Legacy__lean_tests__src__enums.enums
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let e_v1 : Tests.Legacy__lean_tests__src__enums.E ← (pure
    Tests.Legacy__lean_tests__src__enums.E.V1);
  let e_v2 : Tests.Legacy__lean_tests__src__enums.E ← (pure
    Tests.Legacy__lean_tests__src__enums.E.V2);
  let e_v3 : Tests.Legacy__lean_tests__src__enums.E ← (pure
    (Tests.Legacy__lean_tests__src__enums.E.V3 (23 : usize)));
  let e_v4 : Tests.Legacy__lean_tests__src__enums.E ← (pure
    (Tests.Legacy__lean_tests__src__enums.E.V4
      (23 : usize) (12 : usize) (1 : usize)));
  let e_v5 : Tests.Legacy__lean_tests__src__enums.E ← (pure
    (Tests.Legacy__lean_tests__src__enums.E.V5
      (f1 := (23 : usize)) (f2 := (43 : usize))));
  let e_v6 : Tests.Legacy__lean_tests__src__enums.E ← (pure
    (Tests.Legacy__lean_tests__src__enums.E.V6
      (f1 := (12 : usize)) (f2 := (13 : usize))));
  let nil ← (pure Tests.Legacy__lean_tests__src__enums.MyList.Nil);
  let cons_1 : (Tests.Legacy__lean_tests__src__enums.MyList usize) ← (pure
    (Tests.Legacy__lean_tests__src__enums.MyList.Cons
      (hd := (1 : usize)) (tl := nil)));
  let cons_2_1 : (Tests.Legacy__lean_tests__src__enums.MyList usize) ← (pure
    (Tests.Legacy__lean_tests__src__enums.MyList.Cons
      (hd := (2 : usize)) (tl := cons_1)));
  (match e_v1 with
    | (Tests.Legacy__lean_tests__src__enums.E.V1 )
      => do Rust_primitives.Hax.Tuple0.mk
    | (Tests.Legacy__lean_tests__src__enums.E.V2 )
      => do Rust_primitives.Hax.Tuple0.mk
    | (Tests.Legacy__lean_tests__src__enums.E.V3 _)
      => do Rust_primitives.Hax.Tuple0.mk
    | (Tests.Legacy__lean_tests__src__enums.E.V4 x1 x2 x3)
      => do
        let y1 : usize ← (pure (← x1 +? x2));
        let y2 : usize ← (pure (← y1 -? x2));
        let y3 : usize ← (pure (← y2 +? x3));
        Rust_primitives.Hax.Tuple0.mk
    | (Tests.Legacy__lean_tests__src__enums.E.V5 (f1 := f1) (f2 := f2))
      => do Rust_primitives.Hax.Tuple0.mk
    | (Tests.Legacy__lean_tests__src__enums.E.V6
        (f1 := f1) (f2 := other_name_for_f2))
      => do Rust_primitives.Hax.Tuple0.mk)