
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

inductive Tests.Legacy__enum_repr__src__lib.EnumWithRepr : Type
| ExplicitDiscr1 : Tests.Legacy__enum_repr__src__lib.EnumWithRepr 
| ExplicitDiscr2 : Tests.Legacy__enum_repr__src__lib.EnumWithRepr 
| ImplicitDiscrEmptyTuple : Tests.Legacy__enum_repr__src__lib.EnumWithRepr 
| ImplicitDiscrEmptyStruct : Tests.Legacy__enum_repr__src__lib.EnumWithRepr 


def Tests.Legacy__enum_repr__src__lib.EnumWithRepr.ExplicitDiscr1.AnonConst :
u16 := 1

def Tests.Legacy__enum_repr__src__lib.EnumWithRepr.ExplicitDiscr2.AnonConst :
u16 := 5

def Tests.Legacy__enum_repr__src__lib.EnumWithRepr
  (x : Tests.Legacy__enum_repr__src__lib.EnumWithRepr)
  : Result u16
  := do
  (match x with
    | (Tests.Legacy__enum_repr__src__lib.EnumWithRepr.ExplicitDiscr1 )
      => do
        Tests.Legacy__enum_repr__src__lib.EnumWithRepr.ExplicitDiscr1.AnonConst
    | (Tests.Legacy__enum_repr__src__lib.EnumWithRepr.ExplicitDiscr2 )
      => do
        Tests.Legacy__enum_repr__src__lib.EnumWithRepr.ExplicitDiscr2.AnonConst
    | (Tests.Legacy__enum_repr__src__lib.EnumWithRepr.ImplicitDiscrEmptyTuple )
      => do
        (← Tests.Legacy__enum_repr__src__lib.EnumWithRepr.ExplicitDiscr2.AnonConst
          +? (1 : u16))
    | (Tests.Legacy__enum_repr__src__lib.EnumWithRepr.ImplicitDiscrEmptyStruct )
      => do
        (← Tests.Legacy__enum_repr__src__lib.EnumWithRepr.ExplicitDiscr2.AnonConst
          +? (2 : u16)))

inductive Tests.Legacy__enum_repr__src__lib.ImplicitReprs : Type
| A : Tests.Legacy__enum_repr__src__lib.ImplicitReprs 
| B : Tests.Legacy__enum_repr__src__lib.ImplicitReprs 
| C : Tests.Legacy__enum_repr__src__lib.ImplicitReprs 
| D : Tests.Legacy__enum_repr__src__lib.ImplicitReprs 
| E : Tests.Legacy__enum_repr__src__lib.ImplicitReprs 
| F : Tests.Legacy__enum_repr__src__lib.ImplicitReprs 
| G : Tests.Legacy__enum_repr__src__lib.ImplicitReprs 
| H : Tests.Legacy__enum_repr__src__lib.ImplicitReprs 
| I : Tests.Legacy__enum_repr__src__lib.ImplicitReprs 


def Tests.Legacy__enum_repr__src__lib.ImplicitReprs.E.AnonConst : u64 := 30

def Tests.Legacy__enum_repr__src__lib.ImplicitReprs
  (x : Tests.Legacy__enum_repr__src__lib.ImplicitReprs)
  : Result u64
  := do
  (match x with
    | (Tests.Legacy__enum_repr__src__lib.ImplicitReprs.A ) => do (0 : u64)
    | (Tests.Legacy__enum_repr__src__lib.ImplicitReprs.B ) => do (1 : u64)
    | (Tests.Legacy__enum_repr__src__lib.ImplicitReprs.C ) => do (2 : u64)
    | (Tests.Legacy__enum_repr__src__lib.ImplicitReprs.D ) => do (3 : u64)
    | (Tests.Legacy__enum_repr__src__lib.ImplicitReprs.E )
      => do Tests.Legacy__enum_repr__src__lib.ImplicitReprs.E.AnonConst
    | (Tests.Legacy__enum_repr__src__lib.ImplicitReprs.F )
      => do
        (← Tests.Legacy__enum_repr__src__lib.ImplicitReprs.E.AnonConst
          +? (1 : u64))
    | (Tests.Legacy__enum_repr__src__lib.ImplicitReprs.G )
      => do
        (← Tests.Legacy__enum_repr__src__lib.ImplicitReprs.E.AnonConst
          +? (2 : u64))
    | (Tests.Legacy__enum_repr__src__lib.ImplicitReprs.H )
      => do
        (← Tests.Legacy__enum_repr__src__lib.ImplicitReprs.E.AnonConst
          +? (3 : u64))
    | (Tests.Legacy__enum_repr__src__lib.ImplicitReprs.I )
      => do
        (← Tests.Legacy__enum_repr__src__lib.ImplicitReprs.E.AnonConst
          +? (4 : u64)))

def Tests.Legacy__enum_repr__src__lib.f
  (_ : Rust_primitives.Hax.Tuple0)
  : Result u32
  := do
  let _x : u16 ← (pure
    (← Rust_primitives.Hax.cast_op
        (← Tests.Legacy__enum_repr__src__lib.EnumWithRepr.ExplicitDiscr2.AnonConst
          +? (0 : u16))));
  (← (← Rust_primitives.Hax.cast_op
        (← Tests.Legacy__enum_repr__src__lib.EnumWithRepr
            Tests.Legacy__enum_repr__src__lib.EnumWithRepr.ImplicitDiscrEmptyTuple))
    +? (← Rust_primitives.Hax.cast_op
        (← Tests.Legacy__enum_repr__src__lib.EnumWithRepr
            Tests.Legacy__enum_repr__src__lib.EnumWithRepr.ImplicitDiscrEmptyStruct)))

def Tests.Legacy__enum_repr__src__lib.f.CONST : Result u16 := do
  (← Rust_primitives.Hax.cast_op
      (← Tests.Legacy__enum_repr__src__lib.EnumWithRepr.ExplicitDiscr1.AnonConst
        +? (0 : u16)))

def Tests.Legacy__enum_repr__src__lib.get_repr
  (x : Tests.Legacy__enum_repr__src__lib.EnumWithRepr)
  : Result u16
  := do
  (← Tests.Legacy__enum_repr__src__lib.EnumWithRepr x)

def Tests.Legacy__enum_repr__src__lib.get_casted_repr
  (x : Tests.Legacy__enum_repr__src__lib.EnumWithRepr)
  : Result u64
  := do
  (← Rust_primitives.Hax.cast_op
      (← Tests.Legacy__enum_repr__src__lib.EnumWithRepr x))