import Hax.Tactic.HaxZify
import Hax.Tactic.HaxMvcgen
import Qq

open Lean Elab Tactic Meta Qq Std.Do

/-- This tactic is supposed to be run on results of `mvcgen` where the postcondition is of the form
`⇓ r => r = ?mvar`. This tactic will analyse the goals produced by `mvcgen` and instantiate the
metavariable accordingly.

For example, `mvcgen` might produce a goal of the form
```
x r : Int32
h : r.toInt = x.toInt + x.toInt
⊢ ((r.toInt == 0) = true) = ?mvar
```
Then this tactic should instantiate `?mvar` with `((x.toInt + x.toInt == 0) = true)`
-/
def haxConstructPure (mvarId : MVarId) : TacticM Unit := do
  -- Find goals that contain `mvar`
  let allGoals ← getGoals
  let goals ← allGoals.filterM
    fun goal => do pure ((← goal.getType).findMVar? (· == mvarId)).isSome
  if (goals.length > 1) then
    throwError m!"hax_construct_pure: `mvcgen generated more than one goal containing the \
      metavariable. This is currently unsupported. Try to remove if-then-else and match-constructs."
  let [goal] := goals
    | throwError m!"hax_construct_pure: No goal contains the metavariable."

  goal.withContext do
    -- Zify:
    let zifyVars ← collectZifyVars
    let goal ← haxZify goal (fun decl => zifyVars.contains decl.fvarId)
    trace `Hax.hax_construct_pure fun () => m!"Goal after `zify`: {goal}"
    -- Subst:
    let goal ← substVars goal
    trace `Hax.hax_construct_pure fun () => m!"Goal after `subst`: {goal}"
    -- Assign the meta-variable by reflexivity
    withAssignableSyntheticOpaque goal.applyRfl
    pruneSolvedGoals
where
  /-- Collect all machine integer variables that should be converted into integers. We want to
  collect all variables `x` with a hypothesis of the form `x.toInt = ...` here. Then,
  `hax_zify` will convert this into a hypothesis of the form `y = ...` for a new integer variable
  `y`, which we can ultimately eliminate using `subst_vars`. -/
  collectZifyVars : MetaM (Std.HashSet FVarId) := do
    let lctx ← getLCtx
    let mut zifyVars := Std.HashSet.emptyWithCapacity lctx.size
    for decl in lctx do
      if !decl.type.isEq then continue
      let lhs := decl.type.getArg! 1
      if !haxZifyTypes.any (fun (_, toInt, _) => lhs.isAppOfArity toInt 1) then continue
      let some fvarId := (lhs.getArg! 0).fvarId?
        | continue
      zifyVars := zifyVars.insert fvarId
    return zifyVars

/-- The `hax_construct_pure` tactic should be applied to goals of the form
```
 { p // ⦃⌜ ... ⌝⦄ ... ⦃⇓ r => ⌜r = p⌝⦄ }
```
Under the hood, it will use `hax_mvcgen` to generate verification conditions for the given Hoare
triple and then generate a suitable value for `p`. The default call to `hax_mvcgen` can be replaced
via the syntax `hax_construct_pure => custom_tactics`.
 -/
syntax (name := hax_construct_pure) "hax_construct_pure" (" => " tacticSeq)? : tactic

@[tactic hax_construct_pure]
def elabHaxConstructPure : Tactic := fun stx => do
  let tac ← match stx with
  | `(tactic| hax_construct_pure => $tac:tacticSeq) => pure tac
  | `(tactic| hax_construct_pure) => `(tacticSeq| hax_mvcgen -trivial <;> intros)
  | _ => throwUnsupportedSyntax

  let goal ← getMainGoal
  let goalType ← goal.getType

  unless goalType.isAppOf ``Subtype do
    throwError m!"hax_construct_pure: Goal must be of the form `\{ p // ... }` (Subtype), \
      but got:\n{goalType}"

  let u ← mkFreshLevelMVar
  let type : Q(Type) ← mkFreshExprMVar (mkSort u) MetavarKind.natural Name.anonymous
  let mvarP : Q($type → Prop) ← mkFreshExprMVar q($type → Prop)
  let mvarVal : Q($type) ← mkFreshExprSyntheticOpaqueMVar type
  replaceMainGoal (← goal.apply q(@Subtype.mk $type $mvarP $mvarVal))
  evalTactic (← `(tactic| intros))
  evalTactic tac
  let goals ← getGoals
  trace `Hax.hax_construct_pure fun () => m!"Goals after `mvcgen`: {goals}"
  haxConstructPure mvarVal.mvarId!
