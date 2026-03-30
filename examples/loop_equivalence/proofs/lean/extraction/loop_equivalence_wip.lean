
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace loop_equivalence

@[spec]
def op (u : u64) : RustM u64 := do (u /? (2 : u64))

attribute [spec] rust_primitives.cmp.UInt64.eq_spec

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

theorem triple_implies {f : RustM α} {Q : _ → _} {p} :
  (⦃ ⌜ True ⌝ ⦄ f ⦃ ⇓?r =>  ⌜ Q r → p ⌝ ⦄) →
  ((⦃ ⌜ True ⌝ ⦄ f ⦃ ⇓r =>  ⌜ Q r ⌝ ⦄) → p) := by sorry

attribute [local grind! .] USize64.toNat_lt_size

set_option hax_mvcgen.specset "int"
set_option maxHeartbeats 1_000_000
theorem g.spec (N : usize) (arr : (RustArray u64 N)) :
    (do pure True : RustM _ ).holds →
    ⦃ ⌜ True ⌝ ⦄
    (g N arr)
    ⦃ ⇓ arr_future => ⌜
         (do arr_future ==? (← (f N arr)): RustM _ ).holds ⌝ ⦄
 := by
   intro h_pre
   hax_mvcgen [g] <;> try grind
   · intros
     hax_mvcgen <;> try grind
   · -- loop step in g
     hax_mvcgen <;> try grind
     intro j
     hax_mvcgen <;> try grind [USize64.toNat_add_of_lt] -- for-spec unfortunately contains a i+1 on machine ints
     · -- j < 2 * i + 1
      simp [BEq.beq]
      expose_names
      rw [USize64.toNat_add_of_lt (by grind)] at h_16
      have : j.toNat < 2 * (i.toNat + 1) := by grind
      apply triple_implies _ h_3
      hax_mvcgen
      intros ht
      apply triple_implies _ (ht j) <;> clear ht
      hax_mvcgen <;> try grind
      · -- j < 2 * i
        have : j.toNat < 2 * i.toNat := by grind
        simp [BEq.beq]
        rw [Vector.getElem_set_ne] at h_18
        rw [Vector.getElem_set_ne] at h_18
        grind
        grind
        grind
      · -- j ≥ 2 * i
        simp [BEq.beq]
        rw [Vector.getElem_set] at h_18
        rw [Vector.getElem_set] at h_18
        rw [Vector.getElem_set_ne] at h_13
        subst_vars
        have : j = r_6 ∨ j = r_1 := by grind
        cases this
        subst_vars
        simp
        grind
        grind
        grind
     · -- j ≥ 2 * (i + 1)
      expose_names
      apply triple_implies _ h_3
      hax_mvcgen
      intros ht
      apply triple_implies _ (ht j) <;> clear ht
      hax_mvcgen <;> try grind
      · grind [USize64.toNat_add_of_lt]
      · rw [USize64.toNat_add_of_lt (by grind)] at h_16
        rw [Vector.getElem_set_ne] at h_19
        rw [Vector.getElem_set_ne] at h_19
        simp [BEq.beq]
        intro h
        subst_vars
        grind
        grind
        grind
   · -- post-condition if N % 2 > 0 (then-branch)
     hax_mvcgen [f] <;> try grind

     · -- [f] loop-invariant at the start of loop
       intros
       hax_mvcgen <;> try grind

     · -- prove that f's loop invariant holds at i + 1 after the body
       expose_names
       hax_mvcgen <;> try grind
       intro j
       hax_mvcgen <;> try grind
       · -- j ≤ i
         by_cases (j = i)
         · subst_vars
           rw [Vector.getElem_set_self]
           rw [ ← UInt64.toNat_div,
              UInt64.toNat_inj] at h_13
           simp
           apply triple_implies _ h_11
           hax_mvcgen <;> try grind
           intros ht
           apply triple_implies _ (ht j)
           hax_mvcgen <;> try grind
         · subst_vars
           rw [Vector.getElem_set_ne] <;> try grind
           apply triple_implies _ h_11
           intros
           hax_mvcgen <;> try grind
           intros ht
           apply triple_implies _ (ht j)
           hax_mvcgen <;> try grind
       · -- j > i
         subst_vars
         rw [Vector.getElem_set_ne] <;> try grind
         apply triple_implies _ h_11
         hax_mvcgen <;> try grind
         intros ht
         apply triple_implies _ (ht j)
         hax_mvcgen <;> try grind
         -- j > N trivially true

     · -- post-condition implied by [f] loop invariant at the end of the loop
       expose_names
       simp [BEq.beq]
       ext i
       apply triple_implies _ h_9 <;> clear h_9
       hax_mvcgen
       intros ht
       apply triple_implies _ (ht (USize64.ofNat i))
       hax_mvcgen <;> try grind
       · intro
         apply triple_implies _ (h_1) <;> clear h_1
         hax_mvcgen
         intros ht
         apply triple_implies _ (ht (USize64.ofNat i))
         hax_mvcgen <;> try grind
         · intro
           subst_vars
           rw [Vector.getElem_set]
           split <;> try grind
         · intro
           subst_vars
           rw [Vector.getElem_set]
           split <;> try grind
   · -- post-condition if N % 2 = 0 (else-branch)
     hax_mvcgen [f] <;> try grind
     · -- [f] loop-invariant at the start of loop
       intros
       hax_mvcgen <;> try grind
     · -- prove that f's loop invariant holds at i + 1 after the body
       expose_names
       hax_mvcgen <;> try grind
       intro j
       hax_mvcgen <;> try grind
       · -- j ≤ i
         by_cases (j = i)
         · subst_vars
           rw [Vector.getElem_set_self]
           rw [ ← UInt64.toNat_div,
              UInt64.toNat_inj] at h_8
           simp
           apply triple_implies _ h_6
           hax_mvcgen
           intros ht
           apply triple_implies _ (ht j)
           hax_mvcgen <;> try grind
         · subst_vars
           rw [Vector.getElem_set_ne] <;> try grind
           apply triple_implies _ h_6
           hax_mvcgen
           intros ht
           apply triple_implies _ (ht j)
           hax_mvcgen <;> try grind
       · -- j > i
         subst_vars
         rw [Vector.getElem_set_ne] <;> try grind
         apply triple_implies _ h_6
         hax_mvcgen
         intros ht
         apply triple_implies _ (ht j)
         hax_mvcgen <;> try grind
         -- j > N trivially true
     · -- post-condition implied by [f] loop invariant at the end of the loop
       expose_names
       suffices r_1 = r_3 by
         rw [this]
         simp [BEq.beq]
       cases r_1
       cases r_3
       expose_names
       suffices toVec = toVec_1 by grind
       ext i
       apply triple_implies _ h_4
       hax_mvcgen
       intros ht
       apply triple_implies _ (ht (USize64.ofNat i))
       hax_mvcgen <;> try grind
       · intro
         apply triple_implies _ h_1
         hax_mvcgen
         intros ht
         apply triple_implies _ (ht (USize64.ofNat i))
         hax_mvcgen <;> try grind
