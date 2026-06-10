
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


namespace new_tests.legacy__enum_repr__lib

inductive EnumWithRepr : Type
| ExplicitDiscr1 : EnumWithRepr
| ExplicitDiscr2 : EnumWithRepr
| ImplicitDiscrEmptyTuple : EnumWithRepr
| ImplicitDiscrEmptyStruct : EnumWithRepr

def EnumWithRepr.ExplicitDiscr1.AnonConst : u16 := (1 : u16)

def EnumWithRepr.ExplicitDiscr2.AnonConst : u16 := (5 : u16)

@[spec]
def EnumWithRepr_cast_to_repr (x : EnumWithRepr) : RustM u16 := do
  match x with
    | (EnumWithRepr.ExplicitDiscr1 ) => do
      (pure EnumWithRepr.ExplicitDiscr1.AnonConst)
    | (EnumWithRepr.ExplicitDiscr2 ) => do
      (pure EnumWithRepr.ExplicitDiscr2.AnonConst)
    | (EnumWithRepr.ImplicitDiscrEmptyTuple ) => do
      (EnumWithRepr.ExplicitDiscr2.AnonConst +? (1 : u16))
    | (EnumWithRepr.ImplicitDiscrEmptyStruct ) => do
      (EnumWithRepr.ExplicitDiscr2.AnonConst +? (2 : u16))

inductive ImplicitReprs : Type
| A : ImplicitReprs
| B : ImplicitReprs
| C : ImplicitReprs
| D : ImplicitReprs
| E : ImplicitReprs
| F : ImplicitReprs
| G : ImplicitReprs
| H : ImplicitReprs
| I : ImplicitReprs

def ImplicitReprs.E.AnonConst : u64 := (30 : u64)

@[spec]
def ImplicitReprs_cast_to_repr (x : ImplicitReprs) : RustM u64 := do
  match x with
    | (ImplicitReprs.A ) => do (pure (0 : u64))
    | (ImplicitReprs.B ) => do (pure (1 : u64))
    | (ImplicitReprs.C ) => do (pure (2 : u64))
    | (ImplicitReprs.D ) => do (pure (3 : u64))
    | (ImplicitReprs.E ) => do (pure ImplicitReprs.E.AnonConst)
    | (ImplicitReprs.F ) => do (ImplicitReprs.E.AnonConst +? (1 : u64))
    | (ImplicitReprs.G ) => do (ImplicitReprs.E.AnonConst +? (2 : u64))
    | (ImplicitReprs.H ) => do (ImplicitReprs.E.AnonConst +? (3 : u64))
    | (ImplicitReprs.I ) => do (ImplicitReprs.E.AnonConst +? (4 : u64))

@[spec]
def f (_ : rust_primitives.hax.Tuple0) : RustM u32 := do
  let _x : u16 ←
    (rust_primitives.hax.cast_op
      (← (EnumWithRepr.ExplicitDiscr2.AnonConst +? (0 : u16))) :
      RustM u16);
  ((← (rust_primitives.hax.cast_op
      (← (EnumWithRepr_cast_to_repr EnumWithRepr.ImplicitDiscrEmptyTuple)) :
      RustM u32))
    +? (← (rust_primitives.hax.cast_op
      (← (EnumWithRepr_cast_to_repr EnumWithRepr.ImplicitDiscrEmptyStruct)) :
      RustM u32)))

def f.CONST : u16 :=
  RustM.of_isOk
    (do
    (rust_primitives.hax.cast_op
      (← (EnumWithRepr.ExplicitDiscr1.AnonConst +? (0 : u16))) :
      RustM u16))
    (by rfl)

@[spec]
def get_repr (x : EnumWithRepr) : RustM u16 := do (EnumWithRepr_cast_to_repr x)

@[spec]
def get_casted_repr (x : EnumWithRepr) : RustM u64 := do
  (rust_primitives.hax.cast_op (← (EnumWithRepr_cast_to_repr x)) : RustM u64)

end new_tests.legacy__enum_repr__lib

