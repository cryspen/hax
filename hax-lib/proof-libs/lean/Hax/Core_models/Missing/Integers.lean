import Hax.Core_models.Extracted

open Lean in
set_option hygiene false in
macro "declare_Hax_convert_from_instances" : command => do
  let mut cmds := #[]
  let tys := [
    ("UInt8", 8, false),
    ("UInt16", 16, false),
    ("UInt32", 32, false),
    ("UInt64", 64, false),
    ("Int8", 8, true),
    ("Int16", 16, true),
    ("Int32", 32, true),
    ("Int64", 64, true)
  ]
  for (ty1, width1, signed1) in tys do
    for (ty2, width2, signed2) in tys do

      if ty1 == ty2 || signed1 != signed2 || width1 < width2 then continue

      let ty1Ident := mkIdent ty1.toName
      let ty2Ident := mkIdent ty2.toName
      let toTy1 := mkIdent ("to" ++ ty1).toName

      cmds := cmds.push $ ← `(
        @[reducible]
        instance : Core_models.Convert.From.AssociatedTypes $ty1Ident $ty2Ident where
        instance : Core_models.Convert.From $ty1Ident $ty2Ident where
          _from := fun x => x.$toTy1
      )
  return ⟨mkNullNode cmds⟩

declare_Hax_convert_from_instances

attribute [hax_bv_decide]
  Core_models.Convert.From._from
