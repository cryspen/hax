
import Hax.core_models.core_models

set_option mvcgen.warning false
open rust_primitives.hax
open Std.Do

namespace core_models.convert

@[reducible] instance {α : Type} {n : usize} : TryInto.AssociatedTypes (RustSlice α) (RustArray α n) where
  Error := core_models.array.TryFromSliceError

instance {α : Type} {n : usize} : TryInto (RustSlice α) (RustArray α n) where
  try_into a :=
   pure (
     if h: a.val.size = n.toNat then
       core_models.result.Result.Ok (.ofVec (a.val.toVector.cast h))
     else
       .Err core_models.array.TryFromSliceError.mk
     )

@[spec]
theorem TryInto.try_into.spec {α : Type} {n: usize} (a: RustSlice α) :
  (h: a.val.size = n.toNat) →
  ⦃ ⌜ True ⌝ ⦄
  (TryInto.try_into (RustSlice α) (RustArray α n) a )
  ⦃ ⇓ r => ⌜ r = .Ok (.ofVec (a.val.toVector.cast h)) ⌝ ⦄ := by
  intro h
  mvcgen [TryInto.try_into]
  grind

end core_models.convert

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
        instance : core_models.convert.From.AssociatedTypes $ty1Ident $ty2Ident where
        instance : core_models.convert.From $ty1Ident $ty2Ident where
          _from := fun x => pure x.$toTy1
      )
  return ⟨mkNullNode cmds⟩

declare_Hax_convert_from_instances

attribute [specset bv, hax_bv_decide]
  core_models.convert.From._from
