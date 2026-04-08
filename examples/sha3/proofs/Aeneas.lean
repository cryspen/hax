import Aeneas.Array
import Aeneas.Ops
import Aeneas.Tactic.HaxMvcgen
import Aeneas.Tactic.HaxMvcgenAt
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

class core.cmp.PartialEq (α β : Type) where
  eq : α → β → Result Bool

open Std in
def core.array.equality.PartialEqArray.eq
  {T : Type} {U : Type} {N : Usize} (partialEqInst : core.cmp.PartialEq T U)
  (a0 : Array T N) (a1 : Array U N) : Result Bool := do
  Array.allM (fun (x, y) => partialEqInst.eq x y) (Array.zip a0.val a1.val)

def core.cmp.PartialEqU64 : core.cmp.PartialEq UInt64 UInt64 := {
  eq := fun a b => pure (a == b)
}

open Std.Do Std in
@[spec]
theorem core.array.equality.PartialEqArray.eq_spec {N : Usize} (a0 : Array U64 N) (a1 : Array U64 N)
    (h : (Q.1 (a0.val == a1.val)).down) :
    ⦃ ⌜ True ⌝ ⦄
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU64 a0 a1
    ⦃ Q ⦄ := sorry

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
