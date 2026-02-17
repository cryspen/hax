import Hax.rust_primitives.RustM
import Hax.rust_primitives.hax
import Hax.rust_primitives.sequence


abbrev RustSlice := Array
abbrev RustVector := Array

@[spec]
def rust_primitives.slice.array_as_slice (α : Type) (n : usize) :
    RustArray α n → RustM (RustSlice α) :=
  fun x => pure (Vector.toArray x)

@[spec]
def rust_primitives.slice.array_map (α : Type) (β : Type) (n : usize) (_ : Type)
    (a : RustArray α n) (f : α -> RustM β) : RustM (RustArray β n) :=
  a.mapM f

@[spec]
def rust_primitives.slice.array_from_fn (α : Type) (n : usize) (_ : Type)
    (f : usize -> RustM α) : RustM (RustArray α n) :=
  (Vector.range n.toNat).mapM fun i => f (USize64.ofNat i)

@[spec]
def rust_primitives.slice.slice_length (α : Type) (s : RustSlice α) : RustM usize :=
  pure (USize64.ofNat s.size)

@[spec]
def rust_primitives.sequence.seq_from_slice (α : Type) (s : RustSlice α) :
    RustM (rust_primitives.sequence.Seq α) :=
  pure s

@[spec]
def rust_primitives.slice.slice_split_at (α : Type) (s : RustSlice α) (mid : usize) :
    RustM (rust_primitives.hax.Tuple2 (RustSlice α) (RustSlice α)) :=
  if mid <= .ofNat s.size then
    pure ⟨s.take mid.toNat, s.drop mid.toNat⟩
  else
    .fail .arrayOutOfBounds

def rust_primitives.slice.slice_slice
  (α : Type) (seq : RustSlice α) (s e : usize) : RustM (RustSlice α) :=
  if s ≤ e && e ≤ .ofNat seq.size then
    pure seq[s.toNat:e.toNat].toArray
  else
    .fail .undef
