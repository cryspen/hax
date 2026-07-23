import Hax.MissingAeneas
import CoreModels

/-! # `for_loop_with_invariant`

This file implements a tactic `for_loop_with_invariant` allows us to replace occurrences of
Aeneas's `loop` constant with a simpler construct `forLoopWithInvariant`, provided that
the original Rust loops is a for-loop. We support for-loops over any integer scalar type
(signed or unsigned) whose `Step` dictionary is recovered from the loop body, without
early returns. -/

set_option autoImplicit false
set_option linter.unusedVariables false

open Lean Std.Do Elab Parser Tactic Meta
open Aeneas CoreModels
open Aeneas.Std hiding namespace core alloc
namespace Hax

/-- A `for i in s..e` loop carrying its invariant as a marker.

The argument `body : ι → β → Result β` takes the current index and accumulator
and returns the new accumulator. The index scalar type `ι` is polymorphic; its
`Step` dictionary is taken as an explicit argument `stepInst`, which the
`for_loop_with_invariant` tactic reads directly off the extracted loop body, so
unsigned uses (over `Usize`) and signed uses (over `I8`, …, `Isize`) are both
supported without any type-class search. The iterator and `ControlFlow` plumbing live
entirely inside this definition. The first argument `_inv` is a marker read off by the
`for_loop_with_invariant` tactic and by spec lemmas; it has no computational role. -/
def forLoopWithInvariant {ι β : Type} (stepInst : core.iter.range.Step ι)
    (_inv : ι → β → Result Prop)
    (body : ι → β → Result β)
    (rng : core.ops.range.Range ι) (init : β) :
    Result β :=
  loop (fun x : core.ops.range.Range ι × β => do
    let (o, r) ←
      core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
        stepInst x.1
    match o with
    | core.option.Option.None => Result.ok (ControlFlow.done x.2)
    | core.option.Option.Some i => do
        let acc' ← body i x.2
        Result.ok (ControlFlow.cont (r, acc'))) (rng, init)

/-! ## Body-extraction helpers (shared between the conv and regular tactics) -/

/-- Substitute every occurrence of `x.2` in `e` by `aFvar`, recognizing both
`Expr.proj Prod 1 x` and `Prod.snd _ _ x` (application) forms. -/
private def substXSnd (e : Expr) (x aFvar : Expr) : Expr :=
  e.replace fun e' =>
    match e' with
    | .proj ``Prod 1 inner => if inner == x then some aFvar else none
    | _ =>
      if e'.isAppOfArity ``Prod.snd 3 && e'.appArg! == x then some aFvar
      else none

/-- Extract the user-level step body from a loop body in the precise shape
produced by Aeneas extraction (after `simp only [← Aeneas.Std.bind_assoc_eq]`)
for a `for i in s..e` Rust loop:
```
Bind.bind (next StepUsize x.1) <|
  Function.uncurry fun o iter1 =>
    <match>.match_1 _motive o
      (fun _ : Unit => Result.ok (ControlFlow.done x.2))
      fun i => Bind.bind userBody fun acc' =>
        Result.ok (ControlFlow.cont (iter1, acc'))
```
Also returns the `Step` dictionary the loop's `next` call is applied to (the argument
of type `core.iter.range.Step _`), so the caller can pass it to `forLoopWithInvariant`
directly instead of relying on type-class search.

Returns `(userBody, stepDict)` with the match-bound index substituted by `jFvar`. -/
private def extractStepBody (jFvar : Expr) (loopBodyInner : Expr) :
    MetaM (Option (Expr × Expr)) := do
  let inner ← whnfR loopBodyInner
  unless inner.isAppOfArity ``Bind.bind 6 do return none
  -- The bound action is the iterator `next` call; recover its `Step` dictionary
  -- argument (the one of type `core.iter.range.Step _`).
  let nextAction := inner.getArg! 4
  let some stepDict ← nextAction.getAppArgs.findSomeM? (fun a => do
      let t ← inferType a
      return if t.isAppOf ``core.iter.range.Step then some a else none)
    | return none
  let cont ← whnfR (inner.getArg! 5)
  unless cont.isAppOfArity ``Aeneas.Std.uncurry 4 do return none
  let uncurryFn ← whnfR (cont.getArg! 3)
  unless uncurryFn.isLambda do return none
  lambdaTelescope uncurryFn fun ys matchExpr => do
    unless ys.size == 2 do return none
    let matchExpr ← whnfR matchExpr
    -- The match-aux application has shape `match_aux motive discr noneCase someCase`
    -- (4+ args). The `someCase` is the last argument and is a `fun i => ...` lambda.
    let matchArgs := matchExpr.getAppArgs
    unless matchArgs.size ≥ 4 do return none
    let someBranch ← whnfR matchArgs.back!
    unless someBranch.isLambda do return none
    lambdaTelescope someBranch fun is bodyInSome => do
      unless is.size == 1 do return none
      let i := is[0]!
      -- bodyInSome = Bind.bind _ _ _ _ userBody (fun acc' => ok (cont (iter1, acc')))
      let bodyInSome ← whnfR bodyInSome
      unless bodyInSome.isAppOfArity ``Bind.bind 6 do return none
      let userBody := bodyInSome.getArg! 4
      let result := userBody.replace fun e' =>
        if e' == i then some jFvar else none
      return some (result, stepDict)

/-- Given a `loop B (Prod.mk _ _ iter init)` expression and an already-elaborated
invariant `inv`, build `Hax.forLoopWithInvariant inv body iter init` by extracting
`body`. Returns the new expression. Throws if the loop body doesn't have the
expected iterator/`ControlFlow.cont` shape. -/
private def buildForLoopWithInvariant
    (loopExpr inv : Expr) : MetaM Expr := do
  unless loopExpr.isAppOfArity ``Aeneas.Std.loop 4 do
    throwError "for_loop_with_invariant: expected a `loop _ _` expression"
  let initialPair := loopExpr.getArg! 3
  unless initialPair.isAppOfArity ``Prod.mk 4 do
    throwError "for_loop_with_invariant: loop's initial argument is not \
      a literal pair `(iter, init)`"
  let iter := initialPair.getArg! 2
  let init := initialPair.getArg! 3
  let elemTy ← inferType init
  let loopBody := loopExpr.getArg! 2
  -- Recover the index scalar type `ι` from the iterator's type
  -- `core.ops.range.Range ι`.
  let ι := (← inferType iter).getArg! 0
  let (stepLambda, stepDict) ← withLocalDeclD `j ι fun j =>
    withLocalDeclD `a elemTy fun a => do
      let loopBody ← whnfR loopBody
      unless loopBody.isLambda do
        throwError "for_loop_with_invariant: loop body is not a lambda"
      lambdaTelescope loopBody fun xs inner => do
        unless xs.size == 1 do
          throwError "for_loop_with_invariant: loop body has unexpected arity"
        let x := xs[0]!
        let inner := substXSnd inner x a
        let some (body, stepDict) ← extractStepBody j inner
          | throwError "for_loop_with_invariant: could not extract the loop \
              step body (expected shape \
              `Bind.bind userBody (fun acc' => ok (cont (_, acc')))`)"
        let stepLambda ← mkLambdaFVars #[j, a] body
        return (stepLambda, stepDict)
  mkAppM ``Hax.forLoopWithInvariant #[stepDict, inv, stepLambda, iter, init]

/-- Elaborate the user-supplied invariant against the expected type
`ι → β → Result Prop`, where `β` is the element type taken from `init` and the index
type `ι` is recovered from the iterator's type `core.ops.range.Range ι`. -/
private def elabInvariant (iter init : Expr) (invStx : Term) : TacticM Expr := do
  let elemTy ← inferType init
  let ι := (← inferType iter).getArg! 0
  let resultProp ← mkAppM ``Aeneas.Std.Result #[mkSort .zero]
  let invType :=
    Expr.forallE `i ι (Expr.forallE `r elemTy resultProp .default) .default
  let inv ← Term.elabTermEnsuringType invStx invType
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars inv

/-! ## Conv tactic

`conv ... => for_loop_with_invariant inv` expects the conv focus to be a
`loop _ _` expression. It normalizes the focused term with
`simp only [← Aeneas.Std.bind_assoc_eq]`, extracts the user-level step body
automatically, and rewrites the focus to
`Hax.forLoopWithInvariant inv body iter init`. -/

syntax (name := for_loop_with_invariant_conv) "for_loop_with_invariant " term : conv

@[tactic for_loop_with_invariant_conv]
def elabForLoopWithInvariantConv : Tactic := fun stx => do
  let invStx : Term := ⟨stx[1]⟩
  -- The focus is the `loop _ _` expression itself; this simp is naturally
  -- scoped to it.
  evalTactic (← `(conv| (try simp only [← Aeneas.Std.bind_assoc_eq])))
  withMainContext do
    let lhs ← instantiateMVars (← Conv.getLhs)
    let initialPair := lhs.getArg! 3
    unless initialPair.isAppOfArity ``Prod.mk 4 do
      throwError "for_loop_with_invariant: loop's initial argument is not \
        a literal pair `(iter, init)`"
    let iter := initialPair.getArg! 2
    let init := initialPair.getArg! 3
    let inv ← elabInvariant iter init invStx
    let newExpr ← buildForLoopWithInvariant lhs inv
    Conv.changeLhs newExpr

/-! ## Regular tactic

`for_loop_with_invariant inv` locates the first `loop _ _` subterm in the goal
and rewrites it to `Hax.forLoopWithInvariant inv body iter init`. It is a thin
wrapper around the conv tactic: `conv in (loop _ _) => for_loop_with_invariant inv`. -/

syntax (name := for_loop_with_invariant) "for_loop_with_invariant " term : tactic

@[tactic for_loop_with_invariant]
def elabForLoopWithInvariant : Tactic := fun stx => do
  let invStx : Term := ⟨stx[1]⟩
  evalTactic (← `(tactic|
    conv in (Aeneas.Std.loop _ _) => for_loop_with_invariant $invStx))

end Hax
