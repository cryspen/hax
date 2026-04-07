import Aeneas.Array
import Aeneas.Ops
import Lean

namespace Aeneas

namespace Std


scoped notation:max n "#usize" => (USize64.ofNat n)
scoped notation:max n "#u64" => (UInt64.ofNat n)


instance : LT Usize := inferInstanceAs (LT USize64)
instance : DecidableLT Usize := inferInstanceAs (DecidableLT USize64)

instance : HXor U64 U64 U64 := inferInstanceAs (HXor UInt64 UInt64 UInt64)


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


initialize do pure () <*
  Lean.Meta.registerSimpAttr `global_simps "dummy simp-attr"
