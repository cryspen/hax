import Hax.rust_primitives.RustM
import Hax.rust_primitives.num
import Hax.rust_primitives.sequence
import Hax.rust_primitives.hax.array
import Hax.Tactic.SpecSet

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

open rust_primitives.sequence

instance usize.instGetElemResultSeq {α} : GetElemResult (Seq α) usize α where
  getElemResult xs i :=
    if h: i.toNat < xs.val.size then pure (xs.val[i])
    else .fail arrayOutOfBounds

instance usize.instGetElemResultVector {α n} : GetElemResult (RustArray α n) usize α where
  getElemResult xs i :=
    if h: i.toNat < n.toNat then pure (xs.toVec[i.toNat])
    else .fail arrayOutOfBounds

instance Nat.instGetElemResultSeq {α} : GetElemResult (Seq α) Nat α where
  getElemResult xs i :=
    if h: i < xs.val.size then pure (xs.val[i])
    else .fail arrayOutOfBounds

instance Nat.instGetElemResultVector {α n} : GetElemResult (RustArray α n) Nat α where
  getElemResult xs i :=
    if h: i < n.toNat then pure (xs.toVec[i])
    else .fail arrayOutOfBounds

@[spec]
theorem Nat.getElemSeqResult_spec
  (α : Type) (a: Seq α) (i: Nat) (h: i < a.val.size) :
  ⦃ ⌜ True ⌝ ⦄
  ( a[i]_? )
  ⦃ ⇓ r => ⌜ r = a.val[i] ⌝ ⦄ :=
  by mvcgen [RustM.ofOption, Nat.instGetElemResultSeq, getElemResult]

@[spec]
theorem Nat.getElemVectorResult_spec
  (α : Type) (n : usize) (a : RustArray α n) (i: Nat) (h : i < n.toNat) :
  ⦃ ⌜ True ⌝ ⦄
  ( a[i]_? )
  ⦃ ⇓ r => ⌜ r = a.toVec[i] ⌝ ⦄ :=
  by mvcgen [Nat.instGetElemResultVector, getElemResult]

@[spec]
theorem usize.getElemSeqResult_spec
  (α : Type) (a: Seq α) (i: usize) (h: i.toNat < a.val.size) :
  ⦃ ⌜ True ⌝ ⦄
  ( a[i]_? )
  ⦃ ⇓ r => ⌜ r = a.val[i.toNat] ⌝ ⦄ :=
  by mvcgen [usize.instGetElemResultSeq, getElemResult]

@[spec]
theorem usize.getElemVectorResult_spec
  (α : Type) (n : usize) (a : RustArray α n) (i : usize) (h : i.toNat < n.toNat) :
  ⦃ ⌜ True ⌝ ⦄
  ( a[i]_? )
  ⦃ ⇓ r => ⌜ r = a.toVec[i.toNat] ⌝ ⦄ :=
  by mvcgen [usize.instGetElemResultVector, getElemResult]
