import Hax.Rust_primitives.RustM
import Hax.Rust_primitives.Num
import Hax.Rust_primitives.Vec
import Hax.Rust_primitives.Tuple

namespace rust_primitives.sequence

abbrev Seq α := Array α

def seq_len (α : Type) (s : Seq α) :
  RustM usize := USize64.ofNat (Array.size s)

def seq_from_boxed_slice (α : Type) (s : RustSlice α) : RustM (Seq α) :=
  pure s

def seq_extend (α : Type) (s1 : Seq α) (s2 : RustSlice α) :
    RustM (Seq α) :=
  if s1.size + s2.size ≤ Int64.maxValue.toNatClampNeg then
    pure (s1.append s2)
  else
    .fail .maximumSizeExceeded

def seq_push (α : Type) (s1 : Seq α) (a : α) :
    RustM (Seq α):=
  if s1.size < Int64.maxValue.toNatClampNeg then
    pure (s1.push a)
  else
    .fail .maximumSizeExceeded

def seq_drain (α : Type) (s: Seq α) (b: usize) (e: usize) :
    RustM (rust_primitives.hax.Tuple2
      (Seq α) (Seq α)) :=
  if b ≤ e && e ≤ s.size then
    pure ⟨s[:e].toArray ++ s[b:].toArray, s[b:e].toArray⟩
  else
    .fail .undef

def seq_remove (α : Type) (s: Seq α) (n: usize) :
    RustM (rust_primitives.hax.Tuple2 (Seq α) α) :=
  if h : n.toNat < s.size then
    pure ⟨s[:n].toArray ++ s[n+1:].toArray, s[n]⟩
  else
    .fail .arrayOutOfBounds

end rust_primitives.sequence
