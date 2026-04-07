import Aeneas.Num
import Aeneas.Result

namespace Aeneas.Std

def Array (α : Type) (n : Usize) := { a : _root_.Array α // a.size = n.toNat}
def Slice (α : Type) := _root_.Array α

def Array.index_usize {α : Type} {n : Usize} (a : Array α n) (i : Usize) : Result α :=
  if h : i.toNat < a.val.size then
    pure (a.val[i.toNat])
  else
    throw .arrayOutOfBounds

open Std.Do

@[spec]
theorem Array.index_usize_spec {α : Type} [Inhabited α] {n : Usize} (a : Array α n) (i : Usize) {Q}
    (h1 : i.toNat ≥ a.val.size → (Q.2.1 Error.arrayOutOfBounds).down)
    (h2 : ∀ (r : α) (h : i.toNat < a.val.size), r = a.val[i.toNat] → (Q.1 r).down) :
    ⦃ ⌜ True ⌝ ⦄
    (index_usize a i)
    ⦃ Q ⦄ := by sorry

def Array.update {α : Type} {n : Usize} (a : Array α n) (i : Usize) (v : α) : Result (Array α n) :=
  if h : i.toNat < a.val.size then
    pure ⟨a.val.set i.toNat v, sorry⟩
  else
    throw Error.arrayOutOfBounds

@[spec]
theorem Array.update_spec {α : Type} [Inhabited α] {n : Usize} (a : Array α n) (i : Usize) (v : α) {Q}
    (h1 : i.toNat ≥ a.val.size → (Q.2.1 Error.arrayOutOfBounds).down)
    (h2 : ∀ r (h : i.toNat < a.val.size), r = a.val.set i.toNat v → (Q.1 ⟨r, sorry⟩).down) :
    ⦃ ⌜ True ⌝ ⦄
    (Array.update a i v)
    ⦃ Q ⦄ := by sorry

def Array.make (n : Usize) (l : List α) : Array α n :=
  ⟨⟨l⟩, sorry⟩

def Array.repeat (n : Usize) (v : α) : Array α n :=
  ⟨Array.replicate n.toNat v, sorry⟩

def Array.to_slice {α : Type} {n : Usize} (a : Array α n) : Slice α :=
  a.val

def Slice.len {α : Type} (s : Slice α) : Usize :=
  USize64.ofNat s.size

end Aeneas.Std
