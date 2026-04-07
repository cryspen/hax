import Aeneas.Num
import Aeneas.Result

namespace Aeneas.Std

def Array (α : Type) (n : Usize) := { a : _root_.Array α // a.size = n.toNat}
def Slice (α : Type) := _root_.Array α

def Array.index_usize {α : Type} {n : Usize} (a : Array α n) (i : Usize) : Result α :=
  if h : i.toNat < a.val.size then
    .ok (a.val[i.toNat])
  else
    .fail .arrayOutOfBounds

def Array.update {α : Type} {n : Usize} (a : Array α n) (i : Usize) (v : α) : Result (Array α n) :=
  if h : i.toNat < a.val.size then
    .ok ⟨a.val.set i.toNat v, sorry⟩
  else
    .fail .arrayOutOfBounds

def Array.make (n : Usize) (l : List α) : Array α n :=
  ⟨⟨l⟩, sorry⟩

def Array.repeat (n : Usize) (v : α) : Array α n :=
  ⟨Array.replicate n.toNat v, sorry⟩

def Array.to_slice {α : Type} {n : Usize} (a : Array α n) : Slice α :=
  a.val

def Slice.len {α : Type} (s : Slice α) : Usize :=
  USize64.ofNat s.size

end Aeneas.Std
