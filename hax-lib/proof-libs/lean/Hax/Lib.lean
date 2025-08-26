/-
Hax Lean Backend - Cryspen

This library provides the Lean prelude for hax extracted rust-code. It contains
the lean definition of rust (and hax) primitives and intrinsics.

It borrows some definitions from the Aeneas project
(https://github.com/AeneasVerif/aeneas/)
-/

import Hax.Result
import Hax.BitVec
import Hax.Integers

open Error

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

/-
  Logic predicates introduced by Hax (in pre/post conditions)
-/
section Logic

@[simp, spec]
abbrev hax_logical_op_and := (fun a b => a && b)
@[simp, spec]
abbrev hax_logical_op_or := (fun a b => a || b)

abbrev assert (b:Bool) : Result Unit :=
  if b then pure ()
  else .fail (Error.assertionFailure)

abbrev assume : Prop -> Result Unit := fun _ => pure ()

abbrev prop_constructors_from_bool (b :Bool) : Prop := (b = true)

end Logic

/-

# Tuples

-/
section Tuples

abbrev hax_Tuple0 : Type := Unit
def constr_hax_Tuple0 : hax_Tuple0 := ()
instance : CoeDep Type hax_Tuple0 (hax_Tuple0) where
  coe := ()


abbrev hax_Tuple1 (α: Type) : Type := α × Unit
def constr_hax_Tuple1 {hax_Tuple1_Tuple0: α} : hax_Tuple1 α := (hax_Tuple1_Tuple0, ())

abbrev hax_Tuple2 (α β: Type) : Type := α × β
def constr_hax_Tuple2 {α β} {hax_Tuple2_Tuple0: α} {hax_Tuple2_Tuple1 : β} : hax_Tuple2 α β
  := (hax_Tuple2_Tuple0, hax_Tuple2_Tuple1)

end Tuples


/-

# Casts

-/
section Cast

/-- Hax-introduced explicit cast. It is partial (returns a `Result`) -/
@[simp, spec]
def convert_From_from {α β} [Coe α (Result β)] (x:α) : (Result β) := x

/-- Rust-supported casts on base types -/
class Cast (α β: Type) where
  cast : α → Result β

/-- Wrapping cast, does not fail on overflow -/
@[spec]
instance : Cast i64 i32 where
  cast x := pure (Int64.toInt32 x)

@[spec]
instance : Cast i64 (Result i32) where
  cast x := pure (x.toInt32)

@[spec]
instance : Cast usize u32 where
  cast x := pure (USize.toUInt32 x)

@[simp, spec]
def hax_cast_op {α β} [c: Cast α β] (x:α) : (Result β) := c.cast x

end Cast


/-

# Results

Not to be confused with the underlying `Result` monad of the Lean encoding, the
`result_Result` type models the rust `Result`.

-/
section RustResult

inductive result_Result α β
| ok : α -> result_Result α β
| err : β -> result_Result α β

instance {β : Type} : Monad (fun α => result_Result α β) where
  pure x := .ok x
  bind {α α'} x (f: α -> result_Result α' β) := match x with
  | .ok v => f v
  | .err e => .err e

/-- Rust unwrapping, panics if `x` is not `result_Result.ok _` -/
def result_impl_unwrap (α: Type) (β:Type) (x: result_Result α β) : (Result α) :=
  match x with
  | .ok v => pure v
  | .err _ => .fail .panic

theorem result_impl_unwrap_spec {α β} (x: result_Result α β) v :
  x = result_Result.ok v →
  ⦃ True ⦄
  (result_impl_unwrap α β x)
  ⦃ ⇓ r => r = v ⦄ := by
  intros
  mvcgen [result_impl_unwrap]
  simp ; injections


end RustResult


/-

# Folds

Hax represents for-loops as folds over a range

-/
section Fold

/--

Hax-introduced function for for-loops, represented as a fold of the body of the
loop `body` from index `e` to `s`. If the invariant is not checked at runtime,
only passed around

-/
def hax_folds_fold_range {α}
  (s e : Nat)
  (inv : α -> Nat -> Result Bool)
  (init: α)
  (body : α -> Nat -> Result α) : Result α := do
  if e ≤ s then pure init
  else hax_folds_fold_range (s+1) e inv (← body init s) body

-- Lemma for proof of hax_folds_fold_range property
private
theorem induction_decreasing {e} {P: Nat  → Prop}
  (init: P e)
  (rec: ∀ n, n < e → P (n+1) → P n) :
  ∀ n, n ≤ e → P n
:= by
  intros n h
  by_cases (n = 0)
  . subst_vars
    induction e <;> try grind
  generalize h: (e - n) = d
  have : n = e - d := by omega
  have hlt : d < e := by omega
  rw [this] ; clear h this
  induction d with
  | zero => simp ; grind
  | succ d ih =>
    apply rec <;> try omega
    suffices e - (d + 1) + 1 = e - d by grind
    omega

-- Lemma for proof of hax_folds_fold_range property
private
def induction_decreasing_range {s e} {P: Nat → Nat → Prop} :
  s ≤ e →
  (init: P e e) →
  (rec: ∀ (n : Nat), n < e → s ≤ n → P (n + 1) e → P n e) →
  P s e
:= by intros; apply induction_decreasing (P := fun n => (s ≤ n → P n e)) (e := e) <;> try grind

/--

Nat-based specification for hax_folds_fold_range. It requires that the invariant
holds on the initial value, and that for any index `i` between the start and end
values, executing body of the loop on a value that satisfies the invariant
produces a result that also satisfies the invariant.

-/
@[spec]
theorem hax_folds_fold_range_spec {α}
  (s e : Nat)
  (inv : α -> Nat -> Result Bool)
  (init: α)
  (body : α -> Nat -> Result α) :
  inv init s = pure true →
  s ≤ e →
  (∀ (acc:α) (i:Nat),
    s ≤ i →
    i < e →
    inv acc i = pure true →
    ⦃ True ⦄
    (body acc i)
    ⦃ ⇓ res => inv res (i+1) = pure true ⦄) →
  ⦃ True ⦄
  (hax_folds_fold_range s e inv init body)
  ⦃ ⇓ r => inv r e = pure true ⦄
:= by
  intro h_inv_s h_s_le_e h_body
  revert h_inv_s init
  apply induction_decreasing_range (s := s) (e := e) <;> try grind
  . intros
    unfold hax_folds_fold_range
    mvcgen
    omega
  . intros n _ _ ih acc h_acc
    unfold hax_folds_fold_range
    mvcgen <;> (try grind) <;> try omega
    specialize h_body acc n (by omega) (by omega)
    mspec h_body
    . assumption
    . intro h_r
      apply (ih _ h_r)
      grind

end Fold

/-

# Arrays

Rust arrays, are represented as Lean `Vector` (Lean Arrays of known size)

-/
section RustArray

abbrev RustArray := Vector

inductive array_TryFromSliceError where
  | array_TryFromSliceError

def hax_monomorphized_update_at_update_at_usize {α n}
  (a: Vector α n) (i:Nat) (v:α) : Result (Vector α n) :=
  if h: i < a.size then
    pure ( Vector.set a i v )
  else
    .fail (.arrayOutOfBounds)

@[spec]
theorem hax_monomorphized_update_at_update_at_usize_spec
  {α n} (a: Vector α n) (i:Nat) (v:α) (h: i < a.size) :
  ⦃ True ⦄
  (hax_monomorphized_update_at_update_at_usize a i v)
  ⦃ ⇓ r => r = Vector.set a i v ⦄ := by
  mvcgen [hax_monomorphized_update_at_update_at_usize]


@[spec]
def hax_update_at {α n} (m : Vector α n) (i : Nat) (v : α) : Result (Vector α n) :=
  if i < n then
    pure ( Vector.setIfInBounds m i v)
  else
    .fail (.arrayOutOfBounds)

@[spec]
def hax_repeat {α} (v:α) (n:Nat) : Result (Vector α n) :=
  pure (Vector.replicate n v)


/- Warning : this function has been specialized, it should be turned into a typeclass -/
def convert_TryInto_try_into {α n} (a: Array α) :
   Result (result_Result (Vector α n) array_TryFromSliceError) :=
   pure (
     if h: a.size = n then
       result_Result.ok (Eq.mp (congrArg _ h) a.toVector)
     else
       .err .array_TryFromSliceError
     )

theorem convert_TryInto_try_success_spec {α n} (a: Array α) :
  (h: a.size = n) →
  ⦃ True ⦄
  ( convert_TryInto_try_into a)
  ⦃ ⇓ r => r = .ok (Eq.mp (congrArg _ h) a.toVector) ⦄ := by
  intro h
  mvcgen [result_impl_unwrap_spec, convert_TryInto_try_into]
  apply SPred.pure_intro
  split <;> grind


end RustArray

/-

# Ranges

-/

/-- Type of ranges -/
inductive ops_range_Range (α: Type)  where
| range (r_start r_end : α) : ops_range_Range α

@[simp, spec]
def constr_ops_range_Range {α} (ops_range_Range_start : α) (ops_range_Range_end : α) :=
  ops_range_Range.range ops_range_Range_start ops_range_Range_end


/-

# Polymorphic index access

Hax introduces polymorphic index accesses, for any integer type (returning a
single value) and for ranges (returning an array of values). A typeclass-based
notation `a[i]_?` is introduced to support panicking lookups

-/
section Lookup

/--
The classes `GetElemResult` implement lookup notation `xs[i]_?`.
-/
class GetElemResult (coll : Type u) (idx : Type v) (elem : outParam (Type w)) where
  /--
  The syntax `arr[i]_?` gets the `i`'th element of the collection `arr`. It
  can panic if the index is out of bounds.
  -/
  getElemResult (xs : coll) (i : idx) : Result elem

export GetElemResult (getElemResult)

@[inherit_doc getElemResult]
syntax:max term noWs "[" withoutPosition(term) "]" noWs "_?": term
macro_rules | `($x[$i]_?) => `(getElemResult $x $i)

@[app_unexpander getElemResult] meta def unexpandGetElemResult : Lean.PrettyPrinter.Unexpander
  | `($_ $array $index) => `($array[$index]_?)
  | _ => throw ()

/--

Until the backend introduces notations, a definition for the explicit name
`ops_index_index_index` is provided as a proxy

-/
@[simp, spec]
def ops_index_Index_index {α β γ} (a: α) (i:β) [GetElemResult α β γ] : (Result γ) := a[i]_?


instance Range.instGetElemResultArrayUSize :
  GetElemResult
    (Array α)
    (ops_range_Range usize)
    (Array α) where
  getElemResult xs i := match i with
  | ops_range_Range.range s e =>
    let size := xs.size;
    if s ≤ e && e ≤ size then
      pure ( xs.extract s e )
    else
      Result.fail Error.arrayOutOfBounds

instance Range.instGetElemResultVectorUSize :
  GetElemResult
    (Vector α n)
    (ops_range_Range usize)
    (Array α) where
  getElemResult xs i := match i with
  | ops_range_Range.range s e =>
    if s ≤ e && e ≤ n then
      pure (xs.extract s e).toArray
    else
      Result.fail Error.arrayOutOfBounds


instance USize.instGetElemResultArray {α} : GetElemResult (Array α) usize α where
  getElemResult xs i :=
    if h: i.toNat < xs.size then pure (xs[i])
    else .fail arrayOutOfBounds

instance USize.instGetElemResultVector {α n} : GetElemResult (Vector α n) usize α where
  getElemResult xs i :=
    if h: i.toNat < n then pure (xs[i.toNat])
    else .fail arrayOutOfBounds

instance Nat.instGetElemResultArray {α} : GetElemResult (Array α) Nat α where
  getElemResult xs i :=
    if h: i < xs.size then pure (xs[i])
    else .fail arrayOutOfBounds

instance Nat.instGetElemResultVector {α n} : GetElemResult (Vector α n) Nat α where
  getElemResult xs i :=
    if h: i < n then pure (xs[i])
    else .fail arrayOutOfBounds

@[spec]
theorem Nat.getElemArrayResult_spec
  (α : Type) (a: Array α) (i: Nat) (h: i < a.size) :
  ⦃ ⌜ True ⌝ ⦄
  ( a[i]_? )
  ⦃ ⇓ r => r = a[i] ⦄ :=
  by mvcgen [Result.ofOption, Nat.instGetElemResultArray]

@[spec]
theorem Nat.getElemVectorResult_spec
  (α : Type) (n:Nat) (a: Vector α n) (i: Nat) (h : i < n) :
  ⦃ ⌜ True ⌝ ⦄
  ( a[i]_? )
  ⦃ ⇓ r => r = a[i] ⦄ :=
  by mvcgen [Nat.instGetElemResultVector]

@[spec]
theorem USize.getElemArrayResult_spec
  (α : Type) (a: Array α) (i: usize) (h: i.toNat < a.size) :
  ⦃ ⌜ True ⌝ ⦄
  ( a[i]_? )
  ⦃ ⇓ r => r = a[i.toNat]⦄ :=
  by mvcgen [USize.instGetElemResultArray]

@[spec]
theorem USize.getElemVectorResult_spec
  (α : Type) (n:Nat) (a: Vector α n) (i: usize) (h: i.toNat < n) :
  ⦃ ⌜ True ⌝ ⦄
  ( a[i]_? )
  ⦃ ⇓ r => r = a[i.toNat]⦄ :=
  by mvcgen [USize.instGetElemResultVector]

@[spec]
theorem Range.getElemArrayUSize_spec
  (α : Type) (a: Array α) (s e: usize) :
  s ≤ e →
  e ≤ a.size →
  ⦃ ⌜ True ⌝ ⦄
  ( a[(ops_range_Range.range s e)]_? )
  ⦃ ⇓ r => r = Array.extract a s e ⦄
:= by
  intros
  mvcgen [ops_index_Index_index, Range.instGetElemResultArrayUSize] <;> grind

@[spec]
theorem Range.getElemVectorUSize_spec
  (α : Type) (n: Nat) (a: Vector α n) (s e: usize) :
  s ≤ e →
  e ≤ a.size →
  ⦃ ⌜ True ⌝ ⦄
  ( a[(ops_range_Range.range s e)]_? )
  ⦃ ⇓ r => r = (Vector.extract a s e).toArray ⦄
:= by
  intros
  mvcgen [ops_index_Index_index, Range.instGetElemResultVectorUSize] <;> grind


end Lookup



/-

# Slices

Rust slices are represented as Lean Arrays (variable size)

-/


@[spec]
def unsize {α n} (a: Vector α n) : Result (Array α) :=
  pure (a.toArray)

@[simp, spec]
def slice_impl_len α (a: Array α) : Result usize := pure a.size

/-

# Vectors

Rust vectors are represented as Lean Arrays (variable size)

-/
section RustVectors

abbrev RustVector := Array

def alloc_Global : Type := Unit
def vec_Vec (α: Type) (_Allocator:Type) : Type := Array α

def vec_impl_new (α: Type) (Allocator:Type) : Result (vec_Vec α Allocator) :=
  pure ((List.nil).toArray)

def vec__1_impl_len (α: Type) (Allocator:Type) (x: vec_Vec α Allocator) : Result Nat :=
  pure x.size

def vec__2_impl_extend_from_slice (α Allocator) (x: vec_Vec α Allocator) (y: Array α)
  : Result (vec_Vec α Allocator):=
  pure (x.append y)

def slice_impl_to_vec α (a:  Array α) : Result (vec_Vec α alloc_Global) :=
  pure a

-- For
instance {α n} : Coe (Array α) (Result (Vector α n)) where
  coe x :=
    if h: x.size = n then by
      rw [←h]
      apply pure
      apply (Array.toVector x)
    else .fail (.arrayOutOfBounds)

end RustVectors



/-

# Closures

Rust closures are represented as regular Lean functions. Yet, Rust uses a
typeclass `Fn` when calling a closure, which uncurrifies the arguments. This is
taken care of by the `Fn` class

-/

class Fn α (β : outParam Type) γ where
  call : α → β → γ

instance {α β} : Fn (α → β) (hax_Tuple1 α) β where
  call f x := f x.fst

instance {α β γ} : Fn (α → β → γ) (hax_Tuple2 α β) γ where
  call f x := f x.fst x.snd

def ops_function_Fn_call {α β γ} [Fn α β γ] (f: α) (x: β) : γ := Fn.call f x


-- Miscellaneous
def ops_deref_Deref_deref {α Allocator} (v: vec_Vec α Allocator)
  : Result (Array α)
  := pure v


-- Tactics
macro "hax_bv_decide" : tactic => `(tactic| (
  any_goals (injections <;> subst_vars)
  all_goals try (
    simp [Int32.eq_iff_toBitVec_eq,
          Int32.lt_iff_toBitVec_slt,
          Int32.le_iff_toBitVec_sle,
          Int64.eq_iff_toBitVec_eq,
          Int64.lt_iff_toBitVec_slt,
          Int64.le_iff_toBitVec_sle] at * <;>
    bv_decide;
    done
 )))
