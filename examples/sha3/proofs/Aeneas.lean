import Hax

namespace Aeneas

abbrev Result := RustM
abbrev Error := _root_.Error
abbrev ControlFlow := core_models.ops.control_flow.ControlFlow

namespace Result

def ok {α : Type} (v : α) : Result α := RustM.ok v

end Result

def lift {α : Type} (x : α) : Result α := .ok x

namespace Std

abbrev Usize := USize64
abbrev U64 := UInt64

scoped notation:max n "#usize" => (USize64.ofNat n)
scoped notation:max n "#u64" => (UInt64.ofNat n)

instance : HMul Usize Usize (Result Usize) where
  hMul x y := x *? y

instance : HAdd Usize Usize (Result Usize) where
  hAdd x y := x +? y

instance : HMul U64 U64 (Result U64) where
  hMul x y := x *? y

instance : HAdd U64 U64 (Result U64) where
  hAdd x y := x +? y

instance : LT Usize := inferInstanceAs (LT USize64)
instance : DecidableLT Usize := inferInstanceAs (DecidableLT USize64)

instance : HXor U64 U64 U64 := inferInstanceAs (HXor UInt64 UInt64 UInt64)

abbrev Array (α : Type) (n : Usize) := RustArray α n
abbrev Slice (α : Type) := RustSlice α

def Array.index_usize {α : Type} {n : Usize} (a : Array α n) (i : Usize) : Result α :=
  if h : i.toNat < a.toVec.size then
    .ok (a.toVec.get ⟨i.toNat, h⟩)
  else
    .fail .arrayOutOfBounds

def Array.update {α : Type} {n : Usize} (a : Array α n) (i : Usize) (v : α) : Result (Array α n) :=
  if h : i.toNat < a.toVec.size then
    .ok (.ofVec (a.toVec.set i.toNat v))
  else
    .fail .arrayOutOfBounds

def Array.make (n : Usize) (l : List α) : Array α n :=
  .ofVec (Vector.mk ⟨l⟩ sorry)

def Array.repeat (n : Usize) (v : α) : Array α n :=
  .ofVec (Vector.replicate n.toNat v)

def Array.to_slice {α : Type} {n : Usize} (a : Array α n) : Slice α :=
  ⟨a.toVec.toArray, by sorry⟩

def Slice.len {α : Type} (s : Slice α) : Usize :=
  USize64.ofNat s.val.size

end Std

namespace core.clone

structure Clone (T : Type) where
  clone : T → Result T := fun x => .ok x

def CloneU64 : Clone Std.U64 := {}

end core.clone

namespace core.marker

structure Copy (T : Type) where
  cloneInst : core.clone.Clone T := {}

def CopyU64 : Copy Std.U64 := { cloneInst := core.clone.CloneU64 }

end core.marker

namespace core.array

def CloneArray.clone {T : Type} {n : Std.Usize} (_cloneInst : core.clone.Clone T)
    (a : Std.Array T n) : Result (Std.Array T n) :=
  .ok a

end core.array

namespace core.ops.index

structure Index (Self : Type) (Idx : Type) (Output : Type) where
  index : Self → Idx → Result Output

end core.ops.index

end Aeneas

namespace ControlFlow

def dummy : Nat := sorry

end ControlFlow

register_option linter.dupNamespace : Bool := {
  defValue := false
  descr    := "Dummy option"
}
register_option linter.hashCommand : Bool := {
  defValue := false
  descr    := "Dummy option"
}
