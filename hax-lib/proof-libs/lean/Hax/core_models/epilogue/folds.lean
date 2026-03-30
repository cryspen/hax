import Hax.core_models.core_models
import Hax.Tactic.SpecSet
open Std.Do

set_option mvcgen.warning false
set_option linter.unusedVariables false

/-

# Folds

Hax represents for-loops as folds over a range

-/
section Fold

open core_models.ops.control_flow
open rust_primitives.hax

class rust_primitives.hax.folds {int_type: Type} where
  /-- Encoding of Rust for-loops without early returns -/
  fold_range {α : Type}
    (s e : int_type)
    (inv : α -> int_type -> RustM Prop)
    (init: α)
    (body : α -> int_type -> RustM α) :
    RustM α
  /-- Encoding of Rust for-loops with early returns -/
  fold_range_return  {α_acc α_ret : Type}
    (s e: int_type)
    (inv : α_acc -> int_type -> RustM Prop)
    (init: α_acc)
    (body : α_acc -> int_type ->
      RustM (ControlFlow (ControlFlow α_ret (Tuple2 Tuple0 α_acc)) α_acc )):
    RustM (ControlFlow α_ret α_acc)

attribute [spec] rust_primitives.hax.folds.fold_range
attribute [spec] rust_primitives.hax.folds.fold_range_return

open Lean in
set_option hygiene false in
macro "declare_fold_specs" s:(&"signed" <|> &"unsigned") typeName:ident width:term : command => do
  let tyDot (n : Name) := mkIdent (typeName.getId ++ n)
  let tySimp (n : Name) : TSyntax _ := .mk
    (Syntax.node .none ``Lean.Parser.Tactic.simpLemma #[mkNullNode, mkNullNode, tyDot n])
  let tyRw (n : Name) : TSyntax `Lean.Parser.Tactic.rwRule := .mk
    (Syntax.node .none ``Lean.Parser.Tactic.rwRule #[mkNullNode, tyDot n])
  `(
    /-- Implementation of Rust for-loops without early returns -/
    def $(tyDot `fold_range) {α : Type}
        (s e : $typeName)
        (inv : α -> $typeName -> RustM Prop)
        (init: α)
        (body : α -> $typeName -> RustM α)
        : RustM α := do
        if s < e
        then fold_range (s + 1) e inv (← body init s) body
        else pure init
    termination_by (e - s)
    decreasing_by
      simp only [$(tySimp `sizeOf), Nat.add_lt_add_iff_right]
      exact $(tyDot `sub_succ_lt_self) _ _ (by assumption)

    /-- Implementation of Rust for-loops with early returns -/
    def $(tyDot `fold_range_return) {α_acc α_ret : Type}
        (s e: $typeName)
        (inv : α_acc -> $typeName -> RustM Prop)
        (init: α_acc)
        (body : α_acc -> $typeName ->
          RustM (ControlFlow (ControlFlow α_ret (Tuple2 Tuple0 α_acc)) α_acc )) := do
      if s < e
      then
        match (← body init s) with
        -- Rust: `return`
        | .Break (.Break res ) => pure (ControlFlow.Break res)
        -- Rust: `break`
        | .Break (.Continue ⟨ ⟨ ⟩, res⟩) => pure (ControlFlow.Continue res)
        -- Rust: `continue`
        | .Continue res => fold_range_return (s + 1) e inv res body
      else
        pure (ControlFlow.Continue init)
    termination_by (e - s)
    decreasing_by
      simp only [$(tySimp `sizeOf), Nat.add_lt_add_iff_right]
      exact $(tyDot `sub_succ_lt_self) _ _ (by assumption)

    @[spec]
    instance : @rust_primitives.hax.folds $typeName where
      fold_range := $(tyDot `fold_range)
      fold_range_return := $(tyDot `fold_range_return)

    /-- Specification of Rust for-loops without early returns (for bv_decide) -/
    @[specset bv]
    theorem $(mkIdent (s!"rust_primitives.hax.folds.fold_range_spec_bv_{typeName.getId}").toName) {α}
      (s e : $typeName)
      (inv : α -> $typeName -> RustM Prop)
      (init: α)
      (body : α -> $typeName -> RustM α) :
      s ≤ e →
      (inv init s).holds →
      (∀ (acc : α) (i : $typeName),
        s ≤ i →
        i < e →
        (inv acc i).holds →
        ⦃ ⌜ True ⌝ ⦄
        (body acc i)
        ⦃ ⇓ res => ⌜ (inv res (i+1)).holds ⌝ ⦄) →
      ⦃ ⌜ True ⌝ ⦄
      ($(tyDot `fold_range) s e inv init body)
      ⦃ ⇓ r => ⌜ (inv r e).holds ⌝ ⦄
    := by
      intro h_le h_inv_s h_body
      unfold $(tyDot `fold_range)
      mvcgen
      · mstart
        mspec h_body _ _ ($(tyDot `le_refl) s) (by assumption) h_inv_s
        mspec $(mkIdent (s!"rust_primitives.hax.folds.fold_range_spec_bv_{typeName.getId}").toName)
          <;> grind
      · grind
    termination_by (e - s)
    decreasing_by
      simp only [$(tySimp `sizeOf), Nat.add_lt_add_iff_right]
      exact $(tyDot `sub_succ_lt_self) _ _ (by assumption)

    /-- Specification of Rust for-loops without early returns (for grind) -/
    @[specset int]
    theorem $(mkIdent (s!"rust_primitives.hax.folds.fold_range_spec_int_{typeName.getId}").toName) {α}
        (s e : $typeName)
        (inv : α -> $typeName -> RustM Prop)
        (init: α)
        (body : α -> $typeName -> RustM α) :
        s.toNat ≤ e.toNat →
        (inv init s).holds →
        (∀ (acc : α) (i : $typeName),
          s.toNat ≤ i.toNat →
          i.toNat < e.toNat →
          (inv acc i).holds →
          ⦃ ⌜ True ⌝ ⦄
          (body acc i)
          ⦃ ⇓ res => ⌜ (inv res (i+1)).holds ⌝ ⦄) →
        ⦃ ⌜ True ⌝ ⦄
        ($(tyDot `fold_range) s e inv init body)
        ⦃ ⇓ r => ⌜ (inv r e).holds ⌝ ⦄ := by
      apply $(mkIdent (s!"rust_primitives.hax.folds.fold_range_spec_bv_{typeName.getId}").toName)

  )

declare_fold_specs unsigned UInt8 8
declare_fold_specs unsigned UInt16 16
declare_fold_specs unsigned UInt32 32
declare_fold_specs unsigned UInt64 64
declare_fold_specs unsigned USize64 64


end Fold
