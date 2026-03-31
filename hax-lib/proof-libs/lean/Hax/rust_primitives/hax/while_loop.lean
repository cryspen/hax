import Hax.rust_primitives.RustM
import Hax.rust_primitives.hax_lib
import Hax.MissingLean.Std.Do.Triple.SpecLemmas
import Hax.Tactic.HaxConstructPure

open Std.Do

/-

# Loops

-/
open Lean

/-- `while_loop` is used to represent while-loops in `RustM` programs. The function provides
  extra arguments to store a termination measure and an invariant, which can be used to verify the
  program. The arguments `pureInv` and `pureTermination` are usually not provided explicitly and
  derived by the default tactic given below. -/
def rust_primitives.hax.while_loop {β : Type}
    (inv: β → RustM Prop)
    (cond: β → RustM Bool)
    (termination : β -> RustM hax_lib.int.Int)
    (init : β)
    (body : β -> RustM β)
    (pureInv:
        {i : β -> Prop // ∀ b, ⦃⌜ True ⌝⦄ inv b ⦃⇓ r => ⌜ r = (i b) ⌝⦄} := by
      set_option hax_mvcgen.specset "int" in hax_construct_pure <;> grind)
    (_pureTermination :
        {t : β -> Nat // ∀ b, ⦃⌜ True ⌝⦄ termination b ⦃⇓ r => ⌜ r = Int.ofNat (t b) ⌝⦄} := by
      set_option hax_mvcgen.specset "int" in hax_construct_pure <;> grind)
    (pureCond :
        {c : β -> Bool // ∀ b, ⦃⌜ pureInv.val b ⌝⦄ cond b ⦃⇓ r => ⌜ r = c b ⌝⦄} := by
      set_option hax_mvcgen.specset "int" in hax_construct_pure <;> grind) : RustM β :=
  Loop.MonoLoopCombinator.while_loop Loop.mk pureCond.val init body

@[spec]
theorem rust_primitives.hax.while_loop.spec {β : Type}
    (inv: β → RustM Prop)
    (cond: β → RustM Bool)
    (termination: β → RustM hax_lib.int.Int)
    (init : β)
    (body : β -> RustM β)
    (pureInv: {i : β -> Prop // ∀ b, ⦃⌜ True ⌝⦄ inv b ⦃⇓ r => ⌜ r = (i b) ⌝⦄})
    (pureTermination :
      {t : β -> Nat // ∀ b, ⦃⌜ True ⌝⦄ termination b ⦃⇓ r => ⌜ r = Int.ofNat (t b) ⌝⦄})
    (pureCond : {c : β -> Bool // ∀ b, ⦃⌜ pureInv.val b ⌝⦄ cond b ⦃⇓ r => ⌜ r = c b ⌝⦄})
    (step :
      ∀ (b : β), pureCond.val b →
        ⦃⌜ pureInv.val b ⌝⦄
          body b
        ⦃⇓ b' => spred(⌜ pureTermination.val b' < pureTermination.val b ⌝ ∧ ⌜ pureInv.val b' ⌝)⦄ ) :
    ⦃⌜ pureInv.val init ⌝⦄
      while_loop inv cond termination init body pureInv pureTermination pureCond
    ⦃⇓ r => ⌜ pureInv.val r ∧ ¬ pureCond.val r ⌝⦄ :=
  Spec.MonoLoopCombinator.while_loop init Loop.mk pureCond.val body pureInv pureTermination step
