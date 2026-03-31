
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


@[specset int]
def eq_spec (x y : RustArray u64 n) :
  ⦃ ⌜ True ⌝ ⦄
  (x ==? y)
  ⦃ ⇓ r => ⌜ r = (∀ i (hi : i < n.toNat), x.toVec[i] == y.toVec[i]) ⌝ ⦄ := sorry

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
   hax_mvcgen [g, -rust_primitives.cmp.eq, -rust_primitives.cmp.lt] <;> try grind
   · intros
     hax_mvcgen <;> try grind
   · -- loop step in g
     hax_mvcgen <;> try grind
     intro j
     hax_mvcgen <;> try grind
     · -- j < 2 * i + 1
      expose_names
      apply triple_implies _ h_3 <;> clear h_3
      hax_mvcgen
      intros ht
      apply triple_implies _ (ht j) <;> clear ht
      hax_mvcgen <;> try grind
     · -- j ≥ 2 * (i + 1)
      expose_names
      apply triple_implies _ h_3 <;> clear h_3
      hax_mvcgen
      intros ht
      apply triple_implies _ (ht j) <;> clear ht
      hax_mvcgen <;> try grind
   · -- post-condition if N % 2 > 0 (then-branch)
     hax_mvcgen [f, -rust_primitives.cmp.eq, -rust_primitives.cmp.lt] <;> try grind

     · -- [f] loop-invariant at the start of loop
       intros
       hax_mvcgen <;> try grind

     · -- prove that f's loop invariant holds at i + 1 after the body
       expose_names
       hax_mvcgen <;> try grind
       intro j
       hax_mvcgen <;> try grind
       · -- j ≤ i
        subst_vars
        apply triple_implies _ h_11
        intros
        hax_mvcgen <;> try grind
        intros ht
        apply triple_implies _ (ht j)
        by_cases (j = i)
        · hax_mvcgen <;> try grind
        · hax_mvcgen <;> try grind
          rw [Vector.getElem_set_ne] <;> try grind
       · -- j > i
         subst_vars
         apply triple_implies _ h_11
         hax_mvcgen <;> try grind
         intros ht
         apply triple_implies _ (ht j)
         hax_mvcgen <;> try grind
         rw [Vector.getElem_set_ne] <;> try grind
         -- j > N trivially true

     · -- post-condition implied by [f] loop invariant at the end of the loop
       expose_names
       simp only [h_10, beq_iff_eq]
       intros i hi
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
           grind
         · intro
           subst_vars
           rw [Vector.getElem_set]
           grind
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
         · apply triple_implies _ h_6
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
       simp only [h_5, beq_iff_eq]
       intros i hi
       expose_names
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
