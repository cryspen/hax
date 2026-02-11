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
        instance : core_models.convert.From.AssociatedTypes $ty1Ident $ty2Ident where
        instance : core_models.convert.From $ty1Ident $ty2Ident where
          _from := fun x => x.$toTy1
      )
  return ⟨mkNullNode cmds⟩

declare_Hax_convert_from_instances

attribute [hax_bv_decide]
  core_models.convert.From._from

namespace core_models.num.Impl_8

@[spec]
def rotate_left (x: u32) (n: Nat) : RustM u32 :=
  pure (UInt32.ofBitVec (BitVec.rotateLeft x.toBitVec n))

@[spec]
def from_le_bytes (x: Vector u8 4) : u32 :=
  x[0].toUInt32
  + (x[1].toUInt32 <<< 8)
  + (x[2].toUInt32 <<< 16)
  + (x[3].toUInt32 <<< 24)

@[spec]
def to_le_bytes (x:u32) : RustM (Vector u8 4) :=
  #v[
    (x % 256).toUInt8,
    (x >>> 8 % 256).toUInt8,
    (x >>> 16 % 256).toUInt8,
    (x >>> 24 % 256).toUInt8,
  ]

end core_models.num.Impl_8


attribute [spec] core_models.num.Impl_8.wrapping_add
