
import Hax.rust_primitives.RustM
import Hax.rust_primitives.ops

/-

## Wrapping operations

Rust also has total arithmetic operations, renamed by hax (with disambiguator)
for each implementation of typeclasses

-/

namespace rust_primitives.num.Impl_8
@[simp, spec]
def wrapping_add (x y : u32) : RustM u32 := pure (x + y)

@[simp, spec]
def rotate_left (x : u32) (n : Nat) : RustM u32 :=
  pure (UInt32.ofBitVec (BitVec.rotateLeft x.toBitVec n))

@[simp, spec]
def from_le_bytes (x : Vector u8 4) : u32 :=
  x[0].toUInt32
  + (x[1].toUInt32 <<< 8)
  + (x[2].toUInt32 <<< 16)
  + (x[3].toUInt32 <<< 24)

@[simp, spec]
def to_le_bytes (x : u32) : RustM (Vector u8 4) :=
  #v[
    (x % 256).toUInt8,
    (x >>> 8 % 256).toUInt8,
    (x >>> 16 % 256).toUInt8,
    (x >>> 24 % 256).toUInt8,
  ]

end rust_primitives.num.Impl_8
