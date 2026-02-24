import Hax.rust_primitives.RustM
import Hax.rust_primitives.num

structure rust_primitives.sequence.Seq α where
  val : Array α
  size_lt_usizeSize : val.size < USize64.size

attribute [grind .] rust_primitives.sequence.Seq.size_lt_usizeSize
attribute [local grind! .] USize64.toNat_lt_size

@[grind =, simp]
theorem rust_primitives.sequence.Seq.toNat_ofNat_size {α} (m : rust_primitives.sequence.Seq α) :
    (USize64.ofNat m.val.size).toNat = m.val.size :=
  USize64.toNat_ofNat_of_lt' m.size_lt_usizeSize

def rust_primitives.sequence.seq_len (α : Type) (s : rust_primitives.sequence.Seq α) :
  RustM usize := pure (USize64.ofNat s.val.size)

def rust_primitives.sequence.seq_first (α : Type) (s : rust_primitives.sequence.Seq α) : RustM α :=
  if h : s.val.size == 0 then
    .fail .arrayOutOfBounds
  else
    pure (s.val[0]'(by grind))

def rust_primitives.sequence.seq_slice
  (α : Type) (seq : rust_primitives.sequence.Seq α) (s e : usize) : RustM (rust_primitives.sequence.Seq α) :=
  if s ≤ e && e ≤ .ofNat seq.val.size then
    pure ⟨seq.val[s.toNat:e.toNat].toArray, by grind⟩
  else
    .fail .undef
