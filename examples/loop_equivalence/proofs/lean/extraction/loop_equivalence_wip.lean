
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

set_option hax_mvcgen.specset "int"
set_option maxHeartbeats 1_000_000
theorem g.spec (N : usize) (arr : (RustArray u64 N)) :
    (do pure True : RustM _ ).holds →
    ⦃ ⌜ True ⌝ ⦄ (g N arr) ⦃ ⇓
       arr_future => ⌜
         (do arr_future ==? (← (f N arr)): RustM _ ).holds ⌝ ⦄
 := by
   unfold RustM.holds
   intro h_pre
   hax_mvcgen [g] <;> (try grind [RustM.holds]) <;> unfold RustM.holds at *
   · intros
     mvcgen <;> try grind
   · sorry -- integer overflow
   · sorry -- integer overflow
   · sorry -- integer overflow
   · sorry -- integer overflow
   · sorry -- integer overflow
   · sorry -- integer overflow
   · -- loop step in g
     sorry
   · -- post-condition if N % 2 > 0 (then-branch)
     hax_mvcgen [f] <;> (try grind [RustM.holds]) <;> unfold RustM.holds at *

     · -- [f] loop-invariant at the start of loop
       intros
       hax_mvcgen <;> (try grind [RustM.holds]) <;> unfold RustM.holds at *

     · -- prove that f's loop invariant holds at i + 1 after the body
       expose_names
       intro j
       hax_mvcgen <;> try grind
       · -- j ≤ i
         by_cases (j = i)
         · subst_vars
           rw [Vector.getElem_set_self]
           rw [ ← UInt64.toNat_div,
              UInt64.toNat_inj] at h_13
           simp
           apply triple_implies _ (h_11 j)
           hax_mvcgen <;> try grind
         · subst_vars
           rw [Vector.getElem_set_ne] <;> try grind
           apply triple_implies _ (h_11 j)
           hax_mvcgen <;> try grind
       · -- j > i
         subst_vars
         rw [Vector.getElem_set_ne] <;> try grind
         apply triple_implies _ (h_11 j)
         hax_mvcgen <;> try grind
         -- j > N trivially true

     · -- post-condition implied by [f] loop invariant at the end of the loop
       expose_names
       simp [BEq.beq]
       ext i
       apply triple_implies _ (h_9 (USize64.ofNat i)) <;> clear h_9
       hax_mvcgen <;> try grind
       · intro
         apply triple_implies _ (h_1 (USize64.ofNat i)) <;> clear h_1
         hax_mvcgen <;> try grind
         · intro
           subst_vars
           rw [Vector.getElem_set]
           split <;> try grind
           · subst_vars
             simp_all only [beq_iff_eq, USize64.toNat_inj]
             rw [← USize64.toNat_sub_of_le] at * <;> try grind
             expose_names
             simp_all!
             grind
           · subst_vars
             simp_all!
             suffices (i = i % 18446744073709551616) by grind
             grind
         · have : (2*r + 1 = N) := by grind
           simp_all only [decide_eq_true_iff.mp]
           have : (i ≥ (N - 1).toNat) := by
             simp
             rw [ show (N-1) = 2*r by grind]
             simp [decide_eq_false_iff_not.mp] at *
             expose_names
             have : 2 * r.toNat = 2 * r.toNat % 18446744073709551616 := by grind
             rw [← this]
             -- clearly true
             sorry
           have : (i = (N - 1).toNat) := by sorry
           -- clearly true
           sorry
       · sorry -- i < N and i > N

   · -- post-condition if N % 2 = 0 (else-branch)
     hax_mvcgen [f] <;> (try grind [RustM.holds]) <;> unfold RustM.holds at *
     · -- [f] loop-invariant at the start of loop
       intros
       hax_mvcgen <;> (try grind [RustM.holds]) <;> unfold RustM.holds at *
     · -- prove that f's loop invariant holds at i + 1 after the body
       expose_names
       intro j
       hax_mvcgen <;> try grind
       · -- j ≤ i
         by_cases (j = i)
         · subst_vars
           rw [Vector.getElem_set_self]
           rw [ ← UInt64.toNat_div,
              UInt64.toNat_inj] at h_8
           simp
           apply triple_implies _ (h_6 j)
           hax_mvcgen <;> try grind
         · subst_vars
           rw [Vector.getElem_set_ne] <;> try grind
           apply triple_implies _ (h_6 j)
           hax_mvcgen <;> try grind
       · -- j > i
         subst_vars
         rw [Vector.getElem_set_ne] <;> try grind
         apply triple_implies _ (h_6 j)
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
       apply triple_implies _ (h_4 (USize64.ofNat i))
       hax_mvcgen <;> try grind
       · intro
         apply triple_implies _ (h_1 (USize64.ofNat i))
         hax_mvcgen <;> try grind
         intro
         subst_vars
         simp_all
         grind
       · sorry -- i < N and i > N
