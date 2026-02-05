import Hax.Rust_primitives.RustM
import Hax.Rust_primitives.Num

abbrev Rust_primitives.Sequence.Seq α := Array α

def Rust_primitives.Sequence.seq_len (α : Type) (s : Rust_primitives.Sequence.Seq α) :
  RustM usize := USize64.ofNat (Array.size s)

def Rust_primitives.Sequence.seq_first (α : Type) (s : Rust_primitives.Sequence.Seq α) : RustM α :=
  if h : s.size == 0 then
    .fail .arrayOutOfBounds
  else
    s[0]'(by grind)

def Rust_primitives.Sequence.seq_slice
  (α : Type) (seq : Rust_primitives.Sequence.Seq α) (s e : usize) : RustM (Rust_primitives.Sequence.Seq α) :=
  if s ≤ e && e ≤ seq.size then
    pure seq[s:e].toArray
  else
    .fail .undef
