import Lean
import Qq
import Hax.Lib
import Hax.Integers.Spec

open Lean Elab Tactic Meta Qq

macro "hax_bv_decide" c:Lean.Parser.Tactic.optConfig : tactic => `(tactic| (
  simp only [hax_bv_decide] at *; bv_decide $c
))

set_option trace.debug true

open Std.Do

def foldAnd : List Q(Prop) → Q(Prop)
| [] => q(True)
| [p] => p
| p :: ps => q($p ∧ $(foldAnd ps))


-- TODO: separate condition extraction from purification, and MetaM from TacticM
elab "hax_purify" tac:tactic : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let goalDecl ← goal.getDecl
    have goalType : Q(Type) := goalDecl.type

    let p ←
      match goalType with
      | ~q(@Subtype.{0} _ $p) => pure p
      | ~q(@Subtype.{1} _ $p) => pure p
      | _ => Lean.Meta.throwTacticEx `hax_purify goal (m!"unable to run hax_purify on this goal: {goalType}")
    let p1 := p
    let (_, _, p) ← lambdaMetaTelescope p
    let (_, _, p) ← if p.isForall then forallMetaBoundedTelescope p 1 else pure (default, default, p)
    -- let #[v] := v
    --   | Lean.Meta.throwTacticEx `hax_purify goal (m!"expected exactly one lambda-variable: {v}")
    forallTelescope p fun vars (p : Q(Prop)) => do
      match p with
      | ~q(@Std.Do.Triple RustM _ _ Prop $condM _ _) => do

        let some lastGoalFVarId := (← getLCtx).getFVarIds.back?
          | Lean.Meta.throwTacticEx `hax_purify goal (m!"unexpected empty local context")

        if vars.size != 0 && vars.size != 1 then
          Lean.Meta.throwTacticEx `hax_purify goal (m!"expected either 0 or 1 forall-variables: {vars}")
        logInfo m!"{p}"
        -- let p ← if vars.size == 2 then mkLambdaFVars #[v] p else pure p
        logInfo m!"{p}"
        let mvcGoal ← mkFreshExprMVarQ q(⊢ₛ wp⟦$condM⟧ (⇓? r => ⌜r⌝))
        -- `(tactic| mvcgen <;> subst_eqs <;> try simp only [*])
        let vcs ← evalTacticAtRaw tac (Expr.mvarId! mvcGoal)
        let wpcs ← vcs.mapM fun vc => do
          let decl ← vc.getDecl
          let hyps ← withLCtx decl.lctx decl.localInstances getLocalHyps
          let (_, x) ← vc.revertAfter lastGoalFVarId
          pure (← x.getDecl).type
        let wpc : Q(Prop) := foldAnd wpcs
        logInfo vars
        logInfo p1
        let wpc ← if vars.size == 1 then mkLambdaFVars vars wpc else pure wpc
        logInfo p1
        let xs ← goal.applyN (← mkAppOptM `Subtype.mk #[none, p1, wpc]) 1
        replaceMainGoal xs
        evalTactic (← `(tactic| intros))

      | _ => Lean.Meta.throwTacticEx `hax_purify goal (m!"expected triple, got: {p}")



theorem Int32.ofInt_eq_of_toInt_eq {a : Int} {b : Int32} (h : b.toInt = a) : Int32.ofInt a = b := by
  subst_vars; exact (Int32.ofInt_toInt b)

elab "hax_zify" : tactic => do
  let lctx ← getLCtx
  for decl in lctx do
    if !decl.isImplementationDetail && (← isDefEq decl.type (mkConst `Int32)) then
      let var := decl.fvarId
      let hname ← mkFreshUserName `h
      let mvarId ← getMainGoal
      mvarId.withContext do
        let arg := {expr := ← mkAppM `Int32.toInt #[mkFVar var], hName? := hname}
        let (_, newVars, mvarId) ← mvarId.generalizeHyp #[arg] ((← getLocalHyps).map (·.fvarId!))
        mvarId.withContext do
          unless newVars.size == 2 do
            Lean.Meta.throwTacticEx `hax_zify mvarId (m!"expected two variables, got {newVars.size}")

          let mvarType := ((← getMCtx).getDecl mvarId).type
          let val ← mkAppM `Int32.ofInt_eq_of_toInt_eq #[mkFVar newVars[1]!]
          let type ← inferType val
          let newMVarType := mkLet (nondep := true) `h type val mvarType
          let newMVar ← mkFreshExprMVar newMVarType
          mvarId.assign $ newMVar
          let mvarId := newMVar.mvarId!
          let (fvarId, mvarId) ← mvarId.intro1

          -- let (_, mvarId) ← substCore mvarId fvarId (symm := true)

          replaceMainGoal [mvarId]
        -- eval generalize h : Int32.toInt $var = $(mkIdent intVar) at *
        -- evalTactic $ ← `(tactic| replace h := Int32.ofInt_eq_of_toInt_eq h)
        -- evalTactic $ ← `(tactic| subst_vars)

-- generalize h' : r.toInt = x at *
-- replace h' := Int32.ofInt_eq_of_toInt_eq h'

example (r : i32) (h : r.toInt + 1 = 3) : r = 3 := by
  hax_zify
  expose_names
  subst

  --refine have x := 0; ?_

  -- subst_vars
  -- generalize h' : r.toInt = x at *
  -- replace h' := congrArg Int32.ofInt h'
  -- simp only [Int32.ofInt_toInt] at h'
  -- subst_vars


-- example : ⊢ₛ wp⟦do
--   let x : i32 ← pure 15
--   let x : i32 ← (x +? x)
--   pure $ ← (Rust_primitives.Hax.Machine_int.eq x 17)
--   : RustM Prop⟧ (⇓? r => ⌜r⌝) := by
--   mvcgen
--   expose_names
--   generalize r.toInt = x at *
--   subst_eqs
--   simp_all only []
--   all_goals sorry


-- def Playground.square.spec (x : u8)  :
--     Spec
--       (requires := (if x > 10 then pure (x == 15) else pure (x == 2)))
--       (ensures := fun res => (if x > 10 then pure (x == res) else pure (x == 0)))
--       (do pure (x : u8) : RustM _) := {
--   pureRequires := by hax_purify <;> mvcgen <;> grind
--   pureEnsures := by hax_purify <;> mvcgen <;> grind
--   contract := by sorry
-- }
