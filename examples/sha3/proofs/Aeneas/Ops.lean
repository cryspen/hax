import Aeneas.Result
import Aeneas.USize64
import Std.Tactic.Do

namespace Aeneas

theorem UInt64.toNat_add_of_lt {x y : UInt64} (h : x.toNat + y.toNat < 2 ^ 64) :
    (x + y).toNat = x.toNat + y.toNat := BitVec.toNat_add_of_lt h

theorem UInt64.toNat_mul_of_lt {x y : UInt64} (h : x.toNat * y.toNat < 2 ^ 64) :
    (x * y).toNat = x.toNat * y.toNat := BitVec.toNat_mul_of_lt h


/-- Addition on Rust integers. Panics on overflow. -/
instance : HAdd UInt64 UInt64 (Result UInt64) where
  hAdd x y :=
    if x.toNat + y.toNat ≥ 2 ^ 64 then
      throw .integerOverflow
    else pure (x + y)

/-- Multiplication on Rust integers. Panics on overflow. -/
instance : HMul UInt64 UInt64 (Result UInt64) where
  hMul x y :=
    if x.toNat * y.toNat ≥ 2 ^ 64 then
      throw .integerOverflow
    else pure (x * y)

/-- Addition on Rust integers. Panics on overflow. -/
instance : HAdd USize64 USize64 (Result USize64) where
  hAdd x y :=
    if x.toNat + y.toNat ≥ 2 ^ 64 then
      throw .integerOverflow
    else pure (x + y)

/-- Multiplication on Rust integers. Panics on overflow. -/
instance : HMul USize64 USize64 (Result USize64) where
  hMul x y :=
    if x.toNat * y.toNat ≥ 2 ^ 64 then
      throw .integerOverflow
    else pure (x * y)

open Std.Do
set_option mvcgen.warning false

@[spec]
theorem USize64.mul_spec (x y : USize64)
    (h1 : x.toNat * y.toNat ≥ 2 ^ 64 → (Q.2.1 Error.integerOverflow).down)
    (h2 : ∀ r : USize64, r.toNat = x.toNat * y.toNat → (Q.1 r).down) :
    ⦃ ⌜ True ⌝ ⦄
    (x * y)
    ⦃ Q ⦄ := by
  unfold HMul.hMul; dsimp [instHMulUSize64Result]
  mvcgen
  · apply h1 (by assumption)
  · apply h2; rw [USize64.toNat_mul_of_lt]; grind
@[spec]

theorem UInt64.mul_spec (x y : UInt64)
    (h1 : x.toNat * y.toNat ≥ 2 ^ 64 → (Q.2.1 Error.integerOverflow).down)
    (h2 : ∀ r : UInt64, r.toNat = x.toNat * y.toNat → (Q.1 r).down) :
    ⦃ ⌜ True ⌝ ⦄
    (x * y)
    ⦃ Q ⦄ := by
  unfold HMul.hMul; dsimp [instHMulUInt64Result]
  mvcgen
  · apply h1 (by assumption)
  · apply h2; rw [UInt64.toNat_mul_of_lt]; grind

@[spec]
theorem USize64.add_spec (x y : USize64)
    (h1 : x.toNat + y.toNat ≥ 2 ^ 64 → (Q.2.1 Error.integerOverflow).down)
    (h2 : ∀ r : USize64, r.toNat = x.toNat + y.toNat → (Q.1 r).down) :
    ⦃ ⌜ True ⌝ ⦄
    (x + y)
    ⦃ Q ⦄ := by
  unfold HAdd.hAdd; dsimp [instHAddUSize64Result]
  mvcgen
  · apply h1 (by assumption)
  · apply h2; rw [USize64.toNat_add_of_lt]; grind
@[spec]

theorem UInt64.add_spec (x y : UInt64)
    (h1 : x.toNat + y.toNat ≥ 2 ^ 64 → (Q.2.1 Error.integerOverflow).down)
    (h2 : ∀ r : UInt64, r.toNat = x.toNat + y.toNat → (Q.1 r).down) :
    ⦃ ⌜ True ⌝ ⦄
    (x + y)
    ⦃ Q ⦄ := by
  unfold HAdd.hAdd; dsimp [instHAddUInt64Result]
  mvcgen
  · apply h1 (by assumption)
  · apply h2; rw [UInt64.toNat_add_of_lt]; grind
