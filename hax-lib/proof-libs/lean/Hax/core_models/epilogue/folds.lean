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
    (body : α -> int_type -> RustM α)
    (pureInv:
        {i : α -> int_type -> Prop // ∀ a b, ⦃⌜ True ⌝⦄ inv a b ⦃⇓ r => ⌜ r = (i a b) ⌝⦄} := by
      set_option hax_mvcgen.specset "bv" in hax_construct_pure <;> bv_decide) :
    RustM α
  /-- Encoding of Rust for-loops with early returns -/
  fold_range_return  {α_acc α_ret : Type}
    (s e: int_type)
    (inv : α_acc -> int_type -> RustM Prop)
    (init: α_acc)
    (body : α_acc -> int_type ->
      RustM (ControlFlow (ControlFlow α_ret (Tuple2 Tuple0 α_acc)) α_acc ))
    (pureInv:
        {i : α_acc -> int_type -> Prop // ∀ a b, ⦃⌜ True ⌝⦄ inv a b ⦃⇓ r => ⌜ r = (i a b) ⌝⦄} := by
      set_option hax_mvcgen.specset "bv" in hax_construct_pure <;> bv_decide) :
    RustM (ControlFlow α_ret α_acc)

attribute [spec] rust_primitives.hax.folds.fold_range
attribute [spec] rust_primitives.hax.folds.fold_range_return

open Lean in
set_option hygiene false in
macro "declare_fold_specs" s:(&"signed" <|> &"unsigned") typeName:ident width:term : command => do

  let signed ← match s.raw[0].getKind with
  | `signed => pure true
  | `unsigned => pure false
  | _ => throw .unsupportedSyntax

  let tyDot (n : Name) := mkIdent (typeName.getId ++ n)
  let tySimp (n : Name) : TSyntax _ := .mk
    (Syntax.node .none ``Lean.Parser.Tactic.simpLemma #[mkNullNode, mkNullNode, tyDot n])

  let terminationMeasure ← if signed
    then `(term| (e.toInt - s.toInt).toNat)
    else `(term| (e - s))
  let decreasingProof ← if signed then `(tacticSeq|
    have : (s + 1).toInt = s.toInt + 1 := by grind
    grind
  ) else `(tacticSeq|
    simp only [$(tySimp `sizeOf), Nat.add_lt_add_iff_right]
    exact $(tyDot `sub_succ_lt_self) _ _ (by assumption)
  )

  let mut cmds := #[]

  cmds := cmds.push $ ← `(
    /-- Implementation of Rust for-loops without early returns -/
    def $(tyDot `fold_range) {α : Type}
        (s e : $typeName)
        (inv : α -> $typeName -> RustM Prop)
        (init: α)
        (body : α -> $typeName -> RustM α)
        (pureInv: {i : α -> $typeName -> Prop // ∀ a b, ⦃⌜ True ⌝⦄ inv a b ⦃⇓ r => ⌜ r = (i a b) ⌝⦄})
        : RustM α := do
        if s < e
        then fold_range (s + 1) e inv (← body init s) body pureInv
        else pure init
    termination_by $terminationMeasure
    decreasing_by $decreasingProof
  )

  cmds := cmds.push $ ← `(
    /-- Implementation of Rust for-loops with early returns -/
    def $(tyDot `fold_range_return) {α_acc α_ret : Type}
        (s e: $typeName)
        (inv : α_acc -> $typeName -> RustM Prop)
        (init: α_acc)
        (body : α_acc -> $typeName ->
          RustM (ControlFlow (ControlFlow α_ret (Tuple2 Tuple0 α_acc)) α_acc ))
        (pureInv: {i : α_acc -> $typeName -> Prop // ∀ a b, ⦃⌜ True ⌝⦄ inv a b ⦃⇓ r => ⌜ r = (i a b) ⌝⦄}) := do
      if s < e
      then
        match (← body init s) with
        -- Rust: `return`
        | .Break (.Break res ) => pure (ControlFlow.Break res)
        -- Rust: `break`
        | .Break (.Continue ⟨ ⟨ ⟩, res⟩) => pure (ControlFlow.Continue res)
        -- Rust: `continue`
        | .Continue res => fold_range_return (s + 1) e inv res body pureInv
      else
        pure (ControlFlow.Continue init)
    termination_by $terminationMeasure
    decreasing_by $decreasingProof
  )

  cmds := cmds.push $ ← `(
    @[spec]
    instance : @rust_primitives.hax.folds $typeName where
      fold_range := $(tyDot `fold_range)
      fold_range_return := $(tyDot `fold_range_return)
  )

  cmds := cmds.push $ ← `(
    /-- Specification of Rust for-loops without early returns (for bv_decide) -/
    @[specset bv]
    theorem $(mkIdent (s!"rust_primitives.hax.folds.fold_range_spec_bv_{typeName.getId}").toName) {α}
      (s e : $typeName)
      (inv : α -> $typeName -> RustM Prop)
      (pureInv)
      (init: α)
      (body : α -> $typeName -> RustM α) :
      s ≤ e →
      pureInv.val init s →
      (∀ (acc : α) (i : $typeName),
        s ≤ i →
        i < e →
        pureInv.val acc i →
        ⦃ ⌜ True ⌝ ⦄
        (body acc i)
        ⦃ ⇓ res => ⌜ pureInv.val res (i+1) ⌝ ⦄) →
      ⦃ ⌜ True ⌝ ⦄
      ($(tyDot `fold_range) s e inv init body pureInv)
      ⦃ ⇓ r => ⌜ pureInv.val r e ⌝ ⦄
    := by
      intro h_le h_inv_s h_body
      unfold $(tyDot `fold_range)
      mvcgen
      · mstart
        mspec h_body _ _ ($(tyDot `le_refl) s) (by assumption) h_inv_s
        mspec $(mkIdent (s!"rust_primitives.hax.folds.fold_range_spec_bv_{typeName.getId}").toName)
          <;> grind
      · grind
    termination_by $terminationMeasure
    decreasing_by $decreasingProof
  )

  cmds := cmds.push $ ← if signed then `(
    /-- Specification of Rust for-loops on signed integers without early returns (for grind) -/
    @[specset int]
    theorem $(mkIdent (s!"rust_primitives.hax.folds.fold_range_spec_int_{typeName.getId}").toName) {α}
        (s e : $typeName)
        (inv : α -> $typeName -> RustM Prop)
        (pureInv)
        (init: α)
        (body : α -> $typeName -> RustM α) :
        s.toInt ≤ e.toInt →
        pureInv.val init s →
        (∀ (acc : α) (i : $typeName),
          s.toInt ≤ i.toInt →
          i.toInt < e.toInt →
          pureInv.val acc i →
          ⦃ ⌜ True ⌝ ⦄
          (body acc i)
          ⦃ ⇓ res => ⌜ pureInv.val res (i+1) ⌝ ⦄) →
        ⦃ ⌜ True ⌝ ⦄
        ($(tyDot `fold_range) s e inv init body pureInv)
        ⦃ ⇓ r => ⌜ pureInv.val r e ⌝ ⦄ := by
      intro h_le h_inv_s h_body
      apply $(mkIdent (s!"rust_primitives.hax.folds.fold_range_spec_bv_{typeName.getId}").toName)
      · exact $(tyDot `le_iff_toInt_le).mpr h_le
      · exact h_inv_s
      · intro acc i hi_ge hi_lt h_inv
        apply h_body
        · exact $(tyDot `le_iff_toInt_le).mp hi_ge
        · exact $(tyDot `lt_iff_toInt_lt).mp hi_lt
        · exact h_inv
  ) else `(
    /-- Specification of Rust for-loops on unsigned integers without early returns (for grind) -/
    @[specset int]
    theorem $(mkIdent (s!"rust_primitives.hax.folds.fold_range_spec_int_{typeName.getId}").toName) {α}
        (s e : $typeName)
        (inv : α -> $typeName -> RustM Prop)
        (pureInv)
        (init: α)
        (body : α -> $typeName -> RustM α) :
        s.toNat ≤ e.toNat →
        pureInv.val init s →
        (∀ (acc : α) (i : $typeName),
          s.toNat ≤ i.toNat →
          i.toNat < e.toNat →
          pureInv.val acc i →
          ⦃ ⌜ True ⌝ ⦄
          (body acc i)
          ⦃ ⇓ res => ⌜ pureInv.val res (i+1) ⌝ ⦄) →
        ⦃ ⌜ True ⌝ ⦄
        ($(tyDot `fold_range) s e inv init body pureInv)
        ⦃ ⇓ r => ⌜ pureInv.val r e ⌝ ⦄ := by
      apply $(mkIdent (s!"rust_primitives.hax.folds.fold_range_spec_bv_{typeName.getId}").toName)
  )

  return ⟨mkNullNode cmds⟩

declare_fold_specs unsigned UInt8 8
declare_fold_specs unsigned UInt16 16
declare_fold_specs unsigned UInt32 32
declare_fold_specs unsigned UInt64 64
declare_fold_specs unsigned USize64 64

declare_fold_specs signed Int8 8
declare_fold_specs signed Int16 16
declare_fold_specs signed Int32 32
declare_fold_specs signed Int64 64


end Fold
