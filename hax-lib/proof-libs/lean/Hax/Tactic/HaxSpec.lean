import Lean
import Hax.rust_primitives.Spec

namespace Hax.Tactic.HaxSpec

open Lean Meta

private def addContractSpec (declName : Name) (attrKind : AttributeKind) : MetaM Unit := do
  let cinfo ← getConstInfo declName
  let type ← instantiateMVars cinfo.type
  forallTelescope type fun xs bodyType => do
    let bodyType ← whnf bodyType
    unless bodyType.isAppOf ``Spec do
      throwError "@[hax_spec]: expected a definition of type `Spec`, got{indentExpr bodyType}"
    let us := cinfo.levelParams.map mkLevelParam
    let app := mkAppN (mkConst declName us) xs
    let contractVal := mkProj ``Spec 2 app
    let contractType ← inferType contractVal
    let contractType ← deltaExpand contractType (· == declName)
    let closedVal ← mkLambdaFVars xs contractVal
    let closedType ← mkForallFVars xs contractType
    let contractDeclName := declName ++ `contract
    addDecl (.thmDecl {
      name := contractDeclName
      levelParams := cinfo.levelParams
      type := closedType
      value := closedVal
    })
    let specStx := mkNode ``Lean.Parser.Attr.simple #[mkIdent `spec, mkNullNode]
    Attribute.add contractDeclName `spec specStx attrKind

initialize registerBuiltinAttribute {
  name := `hax_spec
  descr := "Registers a `Spec` definition for use with `mvcgen`."
  applicationTime := .afterCompilation
  add := fun declName _stx attrKind => do
    discard <| (addContractSpec declName attrKind).run {} {}
}

end Hax.Tactic.HaxSpec
