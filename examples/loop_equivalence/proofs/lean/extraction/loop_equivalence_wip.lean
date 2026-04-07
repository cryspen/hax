
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Hax.Tactic.HaxMvcgen
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

@[spec]
theorem mul_spec' (x y : USize64)
    (h1 : USize64.mulOverflow x y → (Q.2.1 Error.integerOverflow).down)
    (h2 : ∀ r : USize64, r.toNat = x.toNat * y.toNat → (Q.1 r).down) :
    ⦃ ⌜ True ⌝ ⦄
    (x *? y)
    ⦃ Q ⦄ := by
  hax_mvcgen [rust_primitives.ops.arith.Mul.mul]
  · apply h1 (by assumption)
  · grind [USize64.toNat_mul_of_lt]


@[spec 10000]
theorem getElem_spec (a : RustArray u64 N) (i : usize)
    (h1 : N.toNat ≤ i.toNat → (Q.2.1 Error.arrayOutOfBounds).down)
    (h2 : ∀ (r : u64) (h : i.toNat < N.toNat), r = a.toVec[i.toNat] → (Q.1 r).down) :
    ⦃ ⌜ True ⌝ ⦄
    (a[i]_?)
    ⦃ Q ⦄ := by
  dsimp only [getElemResult, usize.instGetElemResultVector]
  hax_mvcgen
  · apply h2; rfl
  · apply h1; omega

namespace loop_equivalence

@[spec]
def op (u : u64) : RustM u64 := do (u /? (2 : u64))

def f (N : usize) (arr : (RustArray u64 N)) : RustM (RustArray u64 N) := do
  let _initial : (RustArray u64 N) ←
    (core_models.clone.Clone.clone (RustArray u64 N) arr);
  let arr : (RustArray u64 N) ←
    (rust_primitives.hax.folds.fold_range
      (0 : usize)
      N
      (fun arr i =>
        (do
        (hax_lib.prop.constructors.forall
          (fun j =>
            (do
            (hax_lib.prop.constructors.from_bool
              (← if (← (j <? i)) then do
                ((← arr[j]_?) ==? (← (op (← _initial[j]_?))))
              else do
                if (← (j <? N)) then do
                  ((← arr[j]_?) ==? (← _initial[j]_?))
                else do
                  (pure true))) :
            RustM hax_lib.prop.Prop))) :
        RustM hax_lib.prop.Prop))
      arr
      (fun arr i =>
        (do
        let arr : (RustArray u64 N) ←
          (rust_primitives.hax.monomorphized_update_at.update_at_usize
            arr
            i
            (← (op (← arr[i]_?))));
        (pure arr) :
        RustM (RustArray u64 N))));
  (pure arr)

def g (N : usize) (arr : (RustArray u64 N)) : RustM (RustArray u64 N) := do
  let _initial : (RustArray u64 N) ←
    (core_models.clone.Clone.clone (RustArray u64 N) arr);
  let arr : (RustArray u64 N) ←
    (rust_primitives.hax.folds.fold_range
      (0 : usize)
      (← (N /? (2 : usize)))
      (fun arr i =>
        (do
        (hax_lib.prop.constructors.forall
          (fun j =>
            (do
            (hax_lib.prop.constructors.from_bool
              (← if (← (j <? (← ((2 : usize) *? i)))) then do
                ((← arr[j]_?) ==? (← (op (← _initial[j]_?))))
              else do
                if (← (j <? N)) then do
                  ((← arr[j]_?) ==? (← _initial[j]_?))
                else do
                  (pure true))) :
            RustM hax_lib.prop.Prop))) :
        RustM hax_lib.prop.Prop))
      arr
      (fun arr i =>
        (do
        let arr : (RustArray u64 N) ←
          (rust_primitives.hax.monomorphized_update_at.update_at_usize
            arr
            (← ((2 : usize) *? i))
            (← (op (← arr[(← ((2 : usize) *? i))]_?))));
        let arr : (RustArray u64 N) ←
          (rust_primitives.hax.monomorphized_update_at.update_at_usize
            arr
            (← ((← ((2 : usize) *? i)) +? (1 : usize)))
            (← (op (← arr[(← ((← ((2 : usize) *? i)) +? (1 : usize)))]_?))));
        (pure arr) :
        RustM (RustArray u64 N))));
  let arr : (RustArray u64 N) ←
    if (← ((← (N %? (2 : usize))) >? (0 : usize))) then do
      (rust_primitives.hax.monomorphized_update_at.update_at_usize
        arr
        (← (N -? (1 : usize)))
        (← (op (← arr[(← (N -? (1 : usize)))]_?))))
    else do
      (pure arr);
  (pure arr)

instance : BEq (RustArray u64 N) where
  beq a b := (a.toVec = b.toVec)

def stopper : Prop → Prop := id

theorem self_spec (f : RustM α) :
  ⦃ ⌜ True ⌝ ⦄ f ⦃ ⇓?r =>  ⌜ stopper (⦃ ⌜ True ⌝ ⦄ f ⦃ ⇓r' =>  ⌜ r = r' ⌝ ⦄) ⌝ ⦄ := by sorry

-- @[spec]
-- def self_spec_op {a} := self_spec (op a)

@[specset int]
def eq_spec (x y : RustArray u64 n) :
  ⦃ ⌜ True ⌝ ⦄
  (x ==? y)
  ⦃ ⇓ r => ⌜ r = (∀ i (hi : i < n.toNat), x.toVec[i] == y.toVec[i]) ⌝ ⦄ := by
  dsimp [rust_primitives.cmp.eq, BEq.beq, instBEqRustArrayU64_extraction]
  hax_mvcgen
  grind

attribute [local grind! .] USize64.toNat_lt_size

set_option hax_mvcgen.specset "int"
set_option maxHeartbeats 10_000_000
theorem g.spec (N : usize) (arr : (RustArray u64 N)) :
    (do pure True : RustM _ ).holds →
    ⦃ ⌜ True ⌝ ⦄
    (g N arr)
    ⦃ ⇓ arr_future => ⌜
         (do arr_future ==? (← (f N arr)): RustM _ ).holds ⌝ ⦄
 := by
  intro h_pre
  hax_mvcgen [g, f, -rust_primitives.cmp.eq, -rust_primitives.cmp.lt]
    <;> try grind
  --  · -- loop step in g
  · -- j < 2 * i + 1
    expose_names
    apply h_17 a <;> grind
  · -- j ≥ 2 * (i + 1)>
    expose_names
    apply h_17 a <;> grind
  --  · -- post-condition if N % 2 > 0 (then-branch)
  · -- j ≤ i
      expose_names
      apply h_16 a <;> grind (splits := 30)
  · -- j > i
      expose_names
      apply h_16 a <;> grind (splits := 30)
      -- j > N trivially true

  · -- post-condition implied by [f] loop invariant at the end of the loop
    expose_names
    simp only [h_10]
    intro i hi
    apply h_9 (USize64.ofNat i) <;> apply h_11 (USize64.ofNat i) <;> try grind (splits := 30)
  --  · -- post-condition if N % 2 = 0 (else-branch)
  · -- j ≤ i
    expose_names
    apply h_10 a <;> clear h_10 <;> try grind (splits := 30)
  · -- j > i
    expose_names
    apply h_10 a <;> clear h_10 <;> try grind (splits := 30)
    -- j > N trivially true
  · -- post-condition implied by [f] loop invariant at the end of the loop
    expose_names
    simp only [h_4, beq_iff_eq]
    intros i hi
    apply h_3 (USize64.ofNat i) <;> apply h_5 (USize64.ofNat i) <;> try grind (splits := 30)
