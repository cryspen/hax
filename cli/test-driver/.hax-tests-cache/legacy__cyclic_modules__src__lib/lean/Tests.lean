
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

inductive Tests.Legacy__cyclic_modules__src__lib.Typ_b.T1 : Type
| T1 : Tests.Legacy__cyclic_modules__src__lib.Typ_b.T1 


inductive Tests.Legacy__cyclic_modules__src__lib.Typ_a.T : Type
| T : Tests.Legacy__cyclic_modules__src__lib.Typ_b.T1 ->
  Tests.Legacy__cyclic_modules__src__lib.Typ_a.T 


def Tests.Legacy__cyclic_modules__src__lib.Typ_b.T1
  (x : Tests.Legacy__cyclic_modules__src__lib.Typ_b.T1)
  : Result isize
  := do
  (match x with
    | (Tests.Legacy__cyclic_modules__src__lib.Typ_b.T1.T1 ) => do (0 : isize))

inductive Tests.Legacy__cyclic_modules__src__lib.Typ_b.T2 : Type
| T2 : Tests.Legacy__cyclic_modules__src__lib.Typ_a.T ->
  Tests.Legacy__cyclic_modules__src__lib.Typ_b.T2 


inductive Tests.Legacy__cyclic_modules__src__lib.Typ_b.T2Rec : Type
| T2 : Tests.Legacy__cyclic_modules__src__lib.Typ_a.TRec ->
  Tests.Legacy__cyclic_modules__src__lib.Typ_b.T2Rec 


inductive Tests.Legacy__cyclic_modules__src__lib.Typ_b.T1Rec : Type
| T1 : (Alloc.Boxed.Box
      Tests.Legacy__cyclic_modules__src__lib.Typ_b.T2Rec
      Alloc.Alloc.Global) -> Tests.Legacy__cyclic_modules__src__lib.Typ_b.T1Rec 


inductive Tests.Legacy__cyclic_modules__src__lib.Typ_a.TRec : Type
| T : Tests.Legacy__cyclic_modules__src__lib.Typ_b.T1Rec ->
  Tests.Legacy__cyclic_modules__src__lib.Typ_a.TRec 
| Empty : Tests.Legacy__cyclic_modules__src__lib.Typ_a.TRec 
