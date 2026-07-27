import Hax.MissingLean.Init.Prelude

def UInt128.toFin (x : UInt128) : Fin UInt128.size := x.toBitVec.toFin

def UInt128.ofNat (n : @& Nat) : UInt128 := ⟨BitVec.ofNat 128 n⟩

def UInt128.ofNatTruncate (n : Nat) : UInt128 :=
  if h : n < UInt128.size then
    UInt128.ofNatLT n h
  else
    UInt128.ofNatLT (UInt128.size - 1) (by decide)

abbrev Nat.toUInt128 := UInt128.ofNat

def UInt128.toNat (n : UInt128) : Nat := n.toBitVec.toNat

def UInt128.toUInt8 (a : UInt128) : UInt8 := a.toNat.toUInt8
def UInt128.toUInt16 (a : UInt128) : UInt16 := a.toNat.toUInt16
def UInt128.toUInt32 (a : UInt128) : UInt32 := a.toNat.toUInt32
def UInt128.toUInt64 (a : UInt128) : UInt64 := a.toNat.toUInt64
def UInt128.toUSize (a : UInt128) : USize := a.toNat.toUSize

def UInt8.toUInt128 (a : UInt8) : UInt128 := ⟨BitVec.ofNat 128 a.toNat⟩
def UInt16.toUInt128 (a : UInt16) : UInt128 := ⟨BitVec.ofNat 128 a.toNat⟩
def UInt32.toUInt128 (a : UInt32) : UInt128 := ⟨BitVec.ofNat 128 a.toNat⟩
def UInt64.toUInt128 (a : UInt64) : UInt128 := ⟨BitVec.ofNat 128 a.toNat⟩
def USize.toUInt128 (a : USize) : UInt128 := ⟨BitVec.ofNat 128 a.toNat⟩

instance UInt128.instOfNat (n : Nat) : OfNat UInt128 n := ⟨UInt128.ofNat n⟩
