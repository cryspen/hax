
abbrev UInt128.size : Nat := 340282366920938463463374607431768211456

structure UInt128 where
  ofBitVec ::
  toBitVec : BitVec 128

def UInt128.ofNatLT (n : @& Nat) (h : LT.lt n UInt128.size) : UInt128 where
  toBitVec := BitVec.ofNatLT n h

def UInt128.decEq (a b : UInt128) : Decidable (Eq a b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ =>
    dite (Eq n m)
      (fun h => isTrue (h ▸ rfl))
      (fun h => isFalse (fun h' => UInt128.noConfusion h' (fun h' => absurd h' h)))

instance : DecidableEq UInt128 := UInt128.decEq

instance : Inhabited UInt128 where
  default := UInt128.ofNatLT 0 (of_decide_eq_true rfl)
