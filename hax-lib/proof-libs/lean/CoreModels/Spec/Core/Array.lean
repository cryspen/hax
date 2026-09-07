import CoreModels.Core.Funs

/-! # Specs for `core_models::array` -/

namespace CoreModels

open Aeneas
open Aeneas.Std hiding namespace core alloc
open Std.Do WP RustM

set_option mvcgen.warning false

/-! ## `Clone for [T; N]` -/

/-- The fold underlying `array_map`, for a closure that returns its argument
unchanged and leaves its state alone: it rebuilds the list it is given. -/
private theorem foldlM_map_id {T F : Type}
    (inst : core.ops.function.FnMut F T T) (f : F)
    (hid : ∀ x, inst.call_mut f x = ok (x, f)) :
    ∀ (l acc : List T),
      l.foldlM (fun (s : List T × F) (x : T) => do
          let __discr ← inst.call_mut s.2 x
          match __discr with
          | (v, f') => ok (s.1 ++ [v], f')) (acc, f) = ok (acc ++ l, f) := by
  intro l
  induction l with
  | nil => intro acc; simp only [List.foldlM_nil, List.append_nil]; rfl
  | cons x xs ih =>
    intro acc
    simp only [List.foldlM_cons, hid, bind_tc_ok]
    simp [ih]

/-- `array_map` with a closure that returns its argument unchanged is the identity. -/
theorem rust_primitives.slice.array_map_id {T F : Type} {N : Std.Usize}
    (inst : core.ops.function.FnMut F T T) (a : Array T N) (f : F)
    (hid : ∀ x, inst.call_mut f x = ok (x, f)) :
    rust_primitives.slice.array_map inst a f = ok a := by
  unfold rust_primitives.slice.array_map
  split <;> rename_i h <;> rw [foldlM_map_id inst f hid a.val []] at h
  · simp at h
  · simp at h
  · simp only [RustM.ok.injEq] at h
    subst h
    apply congrArg
    apply Subtype.ext
    simp

/-- Cloning an array whose element `clone` is the identity returns it unchanged. -/
theorem core.Array.Insts.CoreCloneClone.clone_id {T : Type} {N : Std.Usize}
    (inst : clone.Clone T) (a : Array T N) (hid : ∀ x, inst.clone x = ok x) :
    core.Array.Insts.CoreCloneClone.clone inst a = ok a := by
  unfold core.Array.Insts.CoreCloneClone.clone core.array.Array.map
  apply rust_primitives.slice.array_map_id
  intro x
  simp [core.array.CloneArray.clone.closure.Insts.CoreOpsFunctionFnMutTupleTT,
    core.array.CloneArray.clone.closure.Insts.CoreOpsFunctionFnMutTupleTT.call_mut, hid]

end CoreModels
