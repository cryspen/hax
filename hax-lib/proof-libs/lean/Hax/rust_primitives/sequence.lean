import Hax.rust_primitives.RustM
import Hax.rust_primitives.num

abbrev rust_primitives.sequence.Seq α := Array α

def rust_primitives.sequence.seq_len (α : Type) (s : rust_primitives.sequence.Seq α) :
  RustM usize := pure (USize64.ofNat (Array.size s))

def rust_primitives.sequence.seq_first (α : Type) (s : rust_primitives.sequence.Seq α) : RustM α :=
  if h : s.size == 0 then
    .fail .arrayOutOfBounds
  else
    pure (s[0]'(by grind))

def rust_primitives.sequence.seq_slice
  (α : Type) (seq : rust_primitives.sequence.Seq α) (s e : usize) : RustM (rust_primitives.sequence.Seq α) :=
  if s ≤ e && e ≤ .ofNat seq.size then
    pure seq[s.toNat:e.toNat].toArray
  else
    .fail .undef
