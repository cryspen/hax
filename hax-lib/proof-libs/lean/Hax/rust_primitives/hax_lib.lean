import Hax.rust_primitives.hax.tuple
import Hax.rust_primitives.RustM
import Hax.Tactic.HaxConstructPure

open rust_primitives.hax
open Std.Do

namespace hax_lib

abbrev prop.Prop := Prop

@[spec] def assert (b:Bool) : RustM Tuple0 :=
  if b then pure ⟨ ⟩
  else .fail (Error.assertionFailure)

@[spec] def assume : Prop -> RustM Tuple0 := fun _ => pure ⟨ ⟩

@[spec] def prop.constructors.from_bool (b : Bool) : RustM Prop := pure (b = true)

@[spec] def prop.Impl.from_bool (b : Bool) : RustM Prop := pure (b = true)

@[spec] def prop.constructors.implies (a b : Prop) : RustM Prop := pure (a → b)
@[spec] def prop.constructors.not     (a : Prop)   : RustM Prop := pure (¬ a)
@[spec] def prop.constructors.and     (a b : Prop) : RustM Prop := pure (a ∧ b)
@[spec] def prop.constructors.or      (a b : Prop) : RustM Prop := pure (a ∨ b)
@[spec] def prop.constructors.eq      (a b : Prop) : RustM Prop := pure (a = b)
@[spec] def prop.constructors.ne      (a b : Prop) : RustM Prop := pure (a ≠ b)

@[spec]
def prop.constructors.forall {α : Type}
    (p : α → RustM Prop)
    (pureP : {p' : α -> Prop // ∀ a, ⦃⌜ True ⌝⦄ p a ⦃⇓ r => ⌜ r = (p' a) ⌝⦄} := by
      set_option hax_mvcgen.specset "int" in hax_construct_pure <;> grind) : RustM Prop :=
  pure (∀ a : α, pureP.val a)

@[spec]
def prop.constructors.exists {α : Type}
    (p : α → RustM Prop)
    (pureP : {p' : α -> Prop // ∀ a, ⦃⌜ True ⌝⦄ p a ⦃⇓ r => ⌜ r = (p' a) ⌝⦄} := by
      set_option hax_mvcgen.specset "int" in hax_construct_pure <;> grind) : RustM Prop :=
  pure (∃ a : α, pureP.val a)

end hax_lib

abbrev hax_lib.int.Int : Type := _root_.Int
