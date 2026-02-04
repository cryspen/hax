import Hax.Rust_primitives.RustM
import Hax.Rust_primitives.Vec
import Hax.Rust_primitives.Array
import Hax.Rust_primitives.Sequence

@[spec]
def Rust_primitives.Slice.array_as_slice (α : Type) (n : usize) :
    RustArray α n → RustM (RustSlice α) :=
  fun x => pure (Vector.toArray x)

@[spec]
def Rust_primitives.Slice.array_map (α : Type) (β : Type) (n : usize) (_ : Type)
    (a : RustArray α n) (f : α -> RustM β) : RustM (RustArray β n) :=
  a.mapM f

@[spec]
def Rust_primitives.Slice.array_from_fn (α : Type) (n : usize) (_ : Type)
    (f : usize -> RustM α) : RustM (RustArray α n) :=
  (Vector.range n).mapM fun i => f (USize64.ofNat i)

@[spec]
def Rust_primitives.Slice.slice_length (α : Type) (s : RustSlice α) : RustM usize :=
  pure (USize64.ofNat s.size)

@[spec]
def Rust_primitives.Sequence.seq_from_slice (α : Type) (s : RustSlice α) :
    RustM (Rust_primitives.Sequence.Seq α) :=
  pure s

@[spec]
def Rust_primitives.Slice.slice_split_at (α : Type) (s : RustSlice α) (mid : usize) :
    RustM (Rust_primitives.Hax.Tuple2 (RustSlice α) (RustSlice α)) :=
  if mid <= s.size then
    pure ⟨s.take mid, s.drop mid⟩
  else
    .fail .arrayOutOfBounds

def Rust_primitives.Slice.slice_slice
  (α : Type) (seq : RustSlice α) (s e : usize) : RustM (RustSlice α) :=
  if s ≤ e && e ≤ seq.size then
    pure seq[s:e].toArray
  else
    .fail .undef
