import Lean
open Lean Elab Command

namespace CoreModels.Command

syntax (name := openHidingNs) "open" ident "hiding" "namespace" ident+ : command

@[command_elab openHidingNs]
def elabOpenHidingNs : CommandElab := fun stx => do
  let nsStx  : Ident                    := ⟨stx[1]⟩
  let subStxs : Array (TSyntax `ident)  := stx[4].getArgs.map (⟨·⟩)

  let ns ← resolveUniqueNamespace nsStx

  let env ← getEnv
  let exceptNames : List Name :=
    env.constants.toList.filterMap fun (nm, _) =>
      if subStxs.any (fun sub => (ns ++ sub.getId).isPrefixOf nm) then
        some (nm.replacePrefix ns .anonymous)
      else
        none

  activateScoped ns
  modifyScope fun s =>
    { s with openDecls := OpenDecl.simple ns exceptNames :: s.openDecls }

end CoreModels.Command
