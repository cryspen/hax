import CoreModels.Spec.RustPrimitives.Slice

/-! # Specs for `core_models::array` -/

namespace CoreModels

open Aeneas
open Aeneas.Std hiding namespace core alloc
open Std.Do WP RustM

set_option mvcgen.warning false

/-! ## `Clone for [T; N]` -/

/-- `array_map` with a closure that returns its argument unchanged is the identity. -/
theorem rust_primitives.slice.array_map_id {T F : Type} {N : Std.Usize}
    (inst : core.ops.function.FnMut F T T) (a : Array T N) (f : F)
    (hid : ∀ x, inst.call_mut f x = ok (x, f)) :
    rust_primitives.slice.array_map inst a f = ok a := by
  have hpure : ∀ x ∈ a.val, ⦃ ⌜ True ⌝ ⦄ inst.call_mut f x ⦃ ⇓ r => ⌜ r.2 = f ⌝ ⦄ :=
    fun x _ => WP.triple_iff_exists_ok.2 ⟨(x, f), hid x, rfl⟩
  obtain ⟨b, hb, hpt⟩ :=
    WP.triple_iff_exists_ok.1 (rust_primitives.slice.array_map_spec inst a f hpure)
  have ha := a.property
  have hbp := b.property
  have : b = a := by
    apply Subtype.ext
    apply List.ext_getElem (by omega)
    intro i _ _
    obtain ⟨y, hy, hyi⟩ := WP.triple_iff_exists_ok.1 (hpt i (by omega))
    rw [hid] at hy
    simp only [RustM.ok.injEq] at hy
    subst hy
    exact hyi.symm
  rw [hb, this]

/-- Cloning an array whose element `clone` is the identity returns it unchanged. -/
theorem core.Array.Insts.CoreCloneClone.clone_id {T : Type} {N : Std.Usize}
    (inst : clone.Clone T) (a : Array T N) (hid : ∀ x, inst.clone x = ok x) :
    core.Array.Insts.CoreCloneClone.clone inst a = ok a := by
  unfold core.Array.Insts.CoreCloneClone.clone core.array.Array.map
  apply rust_primitives.slice.array_map_id
  intro x
  simp [core.array.CloneArray.clone.closure.Insts.CoreOpsFunctionFnMutTupleTT.call_mut, hid]

end CoreModels
