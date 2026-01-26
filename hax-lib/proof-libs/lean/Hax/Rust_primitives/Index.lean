import Hax.Rust_primitives.Range
import Hax.Rust_primitives.RustM
import Hax.Rust_primitives.Num


open Core_models.Ops.Range
open Error
open Std.Do

set_option mvcgen.warning false

/-

# Polymorphic index access

Hax introduces polymorphic index accesses, for any integer type (returning a
single value) and for ranges (returning an array of values). A typeclass-based
notation `a[i]_?` is introduced to support panicking lookups

-/

/--
The classes `GetElemResult` implement lookup notation `xs[i]_?`.
-/
class GetElemResult (coll : Type) (idx : Type) (elem : outParam (Type)) where
  /--
  The syntax `arr[i]_?` gets the `i`'th element of the collection `arr`. It
  can panic if the index is out of bounds.
  -/
  getElemResult (xs : coll) (i : idx) : RustM elem

export GetElemResult (getElemResult)

@[inherit_doc getElemResult]
syntax:max term noWs "[" withoutPosition(term) "]" noWs "_?": term
macro_rules | `($x[$i]_?) => `(getElemResult $x $i)

-- Have lean use the notation when printing
@[app_unexpander getElemResult] meta def unexpandGetElemResult : Lean.PrettyPrinter.Unexpander
  | `($_ $array $index) => `($array[$index]_?)
  | _ => throw ()

/--

Until the backend introduces notations, a definition for the explicit name
`ops.index_index_index` is provided as a proxy

-/
@[simp, spec]
def Core.Ops.Index.Index.index {α β γ} (a: α) (i:β) [GetElemResult α β γ] : (RustM γ) := a[i]_?


instance Range.instGetElemResultArrayUSize64 {α: Type}:
  GetElemResult
    (Array α)
    (Range usize)
    (Array α) where
  getElemResult xs i := match i with
  | ⟨s, e⟩ =>
    let size := xs.size;
    if s ≤ e && e.toNat ≤ size then
      pure ( xs.extract s e )
    else
      RustM.fail Error.arrayOutOfBounds

instance Range.instGetElemResultVectorUSize64 {α : Type} {n : Nat} :
  GetElemResult
    (Vector α n)
    (Range usize)
    (Array α) where
  getElemResult xs i := match i with
  | ⟨s, e⟩ =>
    if s ≤ e && e.toNat ≤ n then
      pure (xs.extract s e).toArray
    else
      RustM.fail Error.arrayOutOfBounds


instance usize.instGetElemResultArray {α} : GetElemResult (Array α) usize α where
  getElemResult xs i :=
    if h: i.toNat < xs.size then pure (xs[i])
    else .fail arrayOutOfBounds

instance usize.instGetElemResultVector {α n} : GetElemResult (Vector α n) usize α where
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
  ⦃ ⇓ r => ⌜ r = a[i] ⌝ ⦄ :=
  by mvcgen [RustM.ofOption, Nat.instGetElemResultArray]

@[spec]
theorem Nat.getElemVectorResult_spec
  (α : Type) (n:Nat) (a: Vector α n) (i: Nat) (h : i < n) :
  ⦃ ⌜ True ⌝ ⦄
  ( a[i]_? )
  ⦃ ⇓ r => ⌜ r = a[i] ⌝ ⦄ :=
  by mvcgen [Nat.instGetElemResultVector]

@[spec]
theorem usize.getElemArrayResult_spec
  (α : Type) (a: Array α) (i: usize) (h: i.toNat < a.size) :
  ⦃ ⌜ True ⌝ ⦄
  ( a[i]_? )
  ⦃ ⇓ r => ⌜ r = a[i.toNat] ⌝ ⦄ :=
  by mvcgen [usize.instGetElemResultArray]

@[spec]
theorem usize.getElemVectorResult_spec
  (α : Type) (n:Nat) (a: Vector α n) (i: usize) (h: i.toNat < n) :
  ⦃ ⌜ True ⌝ ⦄
  ( a[i]_? )
  ⦃ ⇓ r => ⌜ r = a[i.toNat] ⌝ ⦄ :=
  by mvcgen [usize.instGetElemResultVector]

@[spec]
theorem Range.getElemArrayUSize64_spec
  (α : Type) (a: Array α) (s e: usize) :
  s.toNat ≤ e.toNat →
  e.toNat ≤ a.size →
  ⦃ ⌜ True ⌝ ⦄
  ( a[(Range.mk s e)]_? )
  ⦃ ⇓ r => ⌜ r = Array.extract a s e ⌝ ⦄
:= by
  intros
  mvcgen [Core.Ops.Index.Index.index, Range.instGetElemResultArrayUSize64]
  grind [USize64.le_iff_toNat_le]

@[spec]
theorem Range.getElemVectorUSize64_spec
  (α : Type) (n: Nat) (a: Vector α n) (s e: usize) :
  s.toNat ≤ e.toNat →
  e.toNat ≤ a.size →
  ⦃ ⌜ True ⌝ ⦄
  ( a[(Range.mk s e)]_? )
  ⦃ ⇓ r => ⌜ r = (Vector.extract a s e).toArray ⌝ ⦄
:= by
  intros
  mvcgen [Core.Ops.Index.Index.index, Range.instGetElemResultVectorUSize64]
  grind [USize64.le_iff_toNat_le]
