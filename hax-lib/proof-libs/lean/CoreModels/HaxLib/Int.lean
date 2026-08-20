import Aeneas
import CoreModels.Command
import CoreModels.Core.TypesPrologue
import CoreModels.Core.Types
import CoreModels.Core.FunsPrologue
open Aeneas
open Aeneas.Std hiding namespace core
open Result ControlFlow Error
open CoreModels.core
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

/-!
# Model of `hax_lib::int`

`hax_lib::int::Int` is Rust's *mathematical* (unbounded) integer for specs.
-/

namespace hax_lib

/-! ## Arithmetic (`core::ops::arith::*` for `Int`) -/

@[spec]
def int.Int.Insts.CoreOpsArithAddIntInt.add
  : int.Int → int.Int → Result int.Int := fun a b => ok (a + b)

@[spec]
def int.Int.Insts.CoreOpsArithSubIntInt.sub
  : int.Int → int.Int → Result int.Int := fun a b => ok (a - b)

@[spec]
def int.Int.Insts.CoreOpsArithMulIntInt.mul
  : int.Int → int.Int → Result int.Int := fun a b => ok (a * b)

@[spec]
def int.Int.Insts.CoreOpsArithDivIntInt.div
  : int.Int → int.Int → Result int.Int := fun a b => ok (a / b)

@[spec]
def int.Int.Insts.CoreOpsArithNegInt.neg
  : int.Int → Result int.Int := fun a => ok (-a)

@[spec]
def int.Int.rem_euclid
  : int.Int → int.Int → Result int.Int := fun a v => ok (Int.emod a v)

@[spec]
def int.Int.pow2 : int.Int → Result int.Int :=
  fun n => ok ((2 : Int) ^ Int.toNat n)

/-! ## Literal construction (`int!`)

The `int!` macro  lowers (in Rust) to `Int::_unsafe_from_str("<digits>")`, which the
aeneas backend emits as `hax_lib.int.Int._unsafe_from_str (toStr "<digits>")`.
We implement this as a macro yielding a numeral, which leads to simpler verification conditions. -/
open Lean in
macro_rules
  | `(hax_lib.int.Int._unsafe_from_str (toStr $s:str)) => do
    let some n := s.getString.toInt? -- The `int!` macro ensures that this is always an integer
      | Macro.throwErrorAt s
          s!"hax_lib.int.Int._unsafe_from_str: cannot parse \"{s.getString}\" as an integer literal"
    let lit := quote n.natAbs
    if n < 0 then `(Result.ok (-($lit : hax_lib.int.Int)))
    else `(Result.ok ($lit : hax_lib.int.Int))


/-! ## Comparison (`core::cmp::*` instances for `Int`) -/

@[spec] def int.Int.Insts.CoreCmpPartialEqInt :
    cmp.PartialEq int.Int int.Int :=
  { eq := fun a b => ok (a == b), ne := fun a b => ok (a != b) }

@[spec] def int.Int.Insts.CoreCmpPartialOrdInt :
    cmp.PartialOrd int.Int int.Int :=
  { PartialEqInst := int.Int.Insts.CoreCmpPartialEqInt
    partial_cmp := fun a b =>
      ok (option.Option.Some (match compare a b with
                              | .lt => cmp.Ordering.Less
                              | .eq => cmp.Ordering.Equal
                              | .gt => cmp.Ordering.Greater))
    lt := fun a b => ok (match compare a b with | .lt => true | _ => false)
    le := fun a b => ok (match compare a b with | .gt => false | _ => true)
    gt := fun a b => ok (match compare a b with | .gt => true | _ => false)
    ge := fun a b => ok (match compare a b with | .lt => false | _ => true) }

/-- `Ord` for `Int` (from the `#[derive(Ord)]` on `hax_lib::int::Int`). -/
@[spec] def int.Int.Insts.CoreCmpOrd : cmp.Ord int.Int :=
  { EqInst := { PartialEqInst := int.Int.Insts.CoreCmpPartialEqInt }
    PartialOrdInst := int.Int.Insts.CoreCmpPartialOrdInt
    cmp := fun a b =>
      ok (match compare a b with
          | .lt => cmp.Ordering.Less
          | .eq => cmp.Ordering.Equal
          | .gt => cmp.Ordering.Greater) }

/-! ## `ToInt::to_int`: machine int to mathematical int -/

@[spec] def U8.Insts.Hax_libIntToInt.to_int : U8 → Result int.Int := fun x => ok (x.val : Int)
@[spec] def U16.Insts.Hax_libIntToInt.to_int : U16 → Result int.Int := fun x => ok (x.val : Int)
@[spec] def U32.Insts.Hax_libIntToInt.to_int : U32 → Result int.Int := fun x => ok (x.val : Int)
@[spec] def U64.Insts.Hax_libIntToInt.to_int : U64 → Result int.Int := fun x => ok (x.val : Int)
@[spec] def U128.Insts.Hax_libIntToInt.to_int : U128 → Result int.Int := fun x => ok (x.val : Int)
@[spec] def Usize.Insts.Hax_libIntToInt.to_int : Usize → Result int.Int := fun x => ok (x.val : Int)
@[spec] def I8.Insts.Hax_libIntToInt.to_int : I8 → Result int.Int := fun x => ok x.val
@[spec] def I16.Insts.Hax_libIntToInt.to_int : I16 → Result int.Int := fun x => ok x.val
@[spec] def I32.Insts.Hax_libIntToInt.to_int : I32 → Result int.Int := fun x => ok x.val
@[spec] def I64.Insts.Hax_libIntToInt.to_int : I64 → Result int.Int := fun x => ok x.val
@[spec] def I128.Insts.Hax_libIntToInt.to_int : I128 → Result int.Int := fun x => ok x.val
@[spec] def Isize.Insts.Hax_libIntToInt.to_int : Isize → Result int.Int := fun x => ok x.val

/-! ## `Abstraction::lift`: machine int to mathematical int

Same meaning as `to_int` (indeed `to_int` is defined as `self.lift()` in Rust);
emitted under the `Abstraction` instance name when a spec uses `.lift()`. -/

@[spec] def U8.Insts.Hax_libAbstractionAbstractionInt.lift : U8 → Result int.Int := fun x => ok (x.val : Int)
@[spec] def U16.Insts.Hax_libAbstractionAbstractionInt.lift : U16 → Result int.Int := fun x => ok (x.val : Int)
@[spec] def U32.Insts.Hax_libAbstractionAbstractionInt.lift : U32 → Result int.Int := fun x => ok (x.val : Int)
@[spec] def U64.Insts.Hax_libAbstractionAbstractionInt.lift : U64 → Result int.Int := fun x => ok (x.val : Int)
@[spec] def U128.Insts.Hax_libAbstractionAbstractionInt.lift : U128 → Result int.Int := fun x => ok (x.val : Int)
@[spec] def Usize.Insts.Hax_libAbstractionAbstractionInt.lift : Usize → Result int.Int := fun x => ok (x.val : Int)
@[spec] def I8.Insts.Hax_libAbstractionAbstractionInt.lift : I8 → Result int.Int := fun x => ok x.val
@[spec] def I16.Insts.Hax_libAbstractionAbstractionInt.lift : I16 → Result int.Int := fun x => ok x.val
@[spec] def I32.Insts.Hax_libAbstractionAbstractionInt.lift : I32 → Result int.Int := fun x => ok x.val
@[spec] def I64.Insts.Hax_libAbstractionAbstractionInt.lift : I64 → Result int.Int := fun x => ok x.val
@[spec] def I128.Insts.Hax_libAbstractionAbstractionInt.lift : I128 → Result int.Int := fun x => ok x.val
@[spec] def Isize.Insts.Hax_libAbstractionAbstractionInt.lift : Isize → Result int.Int := fun x => ok x.val

/-! ## `Concretization`: mathematical int to machine int -/

def int.Int.to_u8 : int.Int → Result U8 := fun n => if n < 0 then Result.fail .integerOverflow else UScalar.tryMk .U8 (Int.toNat n)
def int.Int.to_u16 : int.Int → Result U16 := fun n => if n < 0 then Result.fail .integerOverflow else UScalar.tryMk .U16 (Int.toNat n)
def int.Int.to_u32 : int.Int → Result U32 := fun n => if n < 0 then Result.fail .integerOverflow else UScalar.tryMk .U32 (Int.toNat n)
def int.Int.to_u64 : int.Int → Result U64 := fun n => if n < 0 then Result.fail .integerOverflow else UScalar.tryMk .U64 (Int.toNat n)
def int.Int.to_u128 : int.Int → Result U128 := fun n => if n < 0 then Result.fail .integerOverflow else UScalar.tryMk .U128 (Int.toNat n)
def int.Int.to_usize : int.Int → Result Usize := fun n => if n < 0 then Result.fail .integerOverflow else UScalar.tryMk .Usize (Int.toNat n)
def int.Int.to_i8 : int.Int → Result I8 := fun n => IScalar.tryMk .I8 n
def int.Int.to_i16 : int.Int → Result I16 := fun n => IScalar.tryMk .I16 n
def int.Int.to_i32 : int.Int → Result I32 := fun n => IScalar.tryMk .I32 n
def int.Int.to_i64 : int.Int → Result I64 := fun n => IScalar.tryMk .I64 n
def int.Int.to_i128 : int.Int → Result I128 := fun n => IScalar.tryMk .I128 n
def int.Int.to_isize : int.Int → Result Isize := fun n => IScalar.tryMk .Isize n

/-! ### Specs for the concretization functions -/

section specs
open Std.Do
set_option mvcgen.warning false

open Lean in
local macro "uconcretize_spec " fn:ident T:ident : command => do
  let specName := mkIdent (fn.getId.appendAfter "_spec")
  let maxId := mkIdent (T.getId ++ `max)
  `(@[spec] theorem $specName {Q} {n : Int}
      (hok : ∀ r : $T, (r.val : Int) = n → PostCond.ok Q r)
      (h : (n < 0 ∨ n > $maxId) → PostCond.fail Q .integerOverflow) :
      ⦃ ⌜ True ⌝ ⦄ $fn n ⦃ Q ⦄ := by
    mvcgen [$fn:term, UScalar.tryMk, UScalar.tryMkOpt, ofOption]
    · simp_all
    · split at *
      · simp_all only [Option.some.injEq]
        subst_vars
        apply hok
        simp_all
      · simp_all
    · apply h; simp_all; scalar_tac)

open Lean in
local macro "iconcretize_spec " fn:ident T:ident : command => do
  let specName := mkIdent (fn.getId.appendAfter "_spec")
  let minId := mkIdent (T.getId ++ `min)
  let maxId := mkIdent (T.getId ++ `max)
  `(@[spec] theorem $specName {Q} {n : Int}
      (hok : ∀ r : $T, r.val = n → PostCond.ok Q r)
      (h : (n < $minId ∨ n > $maxId) → PostCond.fail Q .integerOverflow) :
      ⦃ ⌜ True ⌝ ⦄ $fn n ⦃ Q ⦄ := by
    mvcgen [$fn:term, IScalar.tryMk, IScalar.tryMkOpt, ofOption]
    · split at *
      · simp_all only [Option.some.injEq]
        apply hok
        simp_all
        scalar_tac
      · simp_all
    · split at *
      · simp_all
      · apply h
        scalar_tac)

uconcretize_spec int.Int.to_u8 U8
uconcretize_spec int.Int.to_u16 U16
uconcretize_spec int.Int.to_u32 U32
uconcretize_spec int.Int.to_u64 U64
uconcretize_spec int.Int.to_u128 U128
uconcretize_spec int.Int.to_usize Usize
iconcretize_spec int.Int.to_i8 I8
iconcretize_spec int.Int.to_i16 I16
iconcretize_spec int.Int.to_i32 I32
iconcretize_spec int.Int.to_i64 I64
iconcretize_spec int.Int.to_i128 I128
iconcretize_spec int.Int.to_isize Isize

end specs

end hax_lib
