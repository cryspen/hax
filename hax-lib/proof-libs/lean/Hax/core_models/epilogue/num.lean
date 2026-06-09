import Hax.core_models.core_models

attribute [specset bv, hax_bv_decide]
  core_models.convert.From._from

namespace core_models.num.Impl_8

@[spec]
def rotate_left (x : u32) (n : u32) : RustM u32 :=
  pure (UInt32.ofBitVec (BitVec.rotateLeft x.toBitVec n.toNat))

@[spec]
def from_le_bytes (x : RustArray u8 4) : RustM u32 :=
  pure (x.toVec[0].toUInt32
  + (x.toVec[1].toUInt32 <<< 8)
  + (x.toVec[2].toUInt32 <<< 16)
  + (x.toVec[3].toUInt32 <<< 24))

@[spec]
def to_le_bytes (x : u32) : RustM (RustArray u8 4) :=
  pure (.ofVec #v[
    (x % 256).toUInt8,
    (x >>> 8 % 256).toUInt8,
    (x >>> 16 % 256).toUInt8,
    (x >>> 24 % 256).toUInt8,
  ])

end core_models.num.Impl_8


attribute [spec] core_models.num.Impl_8.wrapping_add
