import Hax.Tactic.SpecSet
import Hax.Tactic.Init

namespace Hax.HaxMvcgen

open Lean Elab Syntax Parser Tactic

def mkMvcgenCall (args: Array Name) (cfgStx : Syntax) (argStx : Syntax) : CoreM Syntax := do
  let cfgStx : TSyntax `Lean.Parser.Tactic.optConfig := .mk cfgStx
  let mut elems := argStx[1].getArgs.getSepElems
  for arg in args do
    elems := elems.push
      (Syntax.node .none ``Lean.Parser.Tactic.simpLemma #[mkNullNode, mkNullNode, mkIdent arg])
  let argStx : TSepArray _ _ := Syntax.TSepArray.ofElems (elems.map .mk)
  let tac := ← `(tactic| mvcgen $cfgStx [$argStx,*])
  pure tac

syntax (name := hax_mvcgen) "hax_mvcgen" optConfig
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "] ")? : tactic

/-- A customized version of the `mvcgen` tactic. It provides `mvcgen` with additional lemmas
gathered from `@[specset X]` annotations, where `X` is the current setting of
`set_option hax_mvcgen.specset`. -/
@[tactic hax_mvcgen]
def elabHaxMvcgen : Tactic := fun stx => do
  let specset := hax_mvcgen.specset.get (← getOptions)
  let cfgStx := stx[1]
  let argStx := stx[2]
  let extState := specSetExt.getState (← getEnv)
  let decls := (extState.getD specset.toName {}).toArray
  let tac ← mkMvcgenCall decls cfgStx argStx
  Tactic.evalTactic tac

end  Hax.HaxMvcgen
