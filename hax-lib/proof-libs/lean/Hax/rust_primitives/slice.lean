import Hax.rust_primitives.RustM
import Hax.rust_primitives.hax
import Hax.rust_primitives.sequence



abbrev RustVector := rust_primitives.sequence.Seq
abbrev RustSlice := rust_primitives.sequence.Seq

attribute [local grind! .] rust_primitives.sequence.Seq.size_lt_usizeSize
attribute [local grind! .] USize64.toNat_lt_size

@[spec]
def rust_primitives.slice.array_as_slice (α : Type) (n : usize) :
    RustArray α n → RustM (RustSlice α) :=
  fun x => pure ⟨Vector.toArray x.toVec, by grind⟩

@[spec]
def rust_primitives.slice.array_map (α : Type) (β : Type) (n : usize) (_ : Type)
    (a : RustArray α n) (f : α -> RustM β) : RustM (RustArray β n) := do
  pure (.ofVec (← a.toVec.mapM (f ·) ))

@[spec]
def rust_primitives.slice.array_from_fn (α : Type) (n : usize) (_ : Type)
    (f : usize -> RustM α) : RustM (RustArray α n) := do
  pure (.ofVec (← (Vector.range n.toNat).mapM fun i => f (USize64.ofNat i)))

@[spec]
def rust_primitives.slice.slice_length (α : Type) (s : RustSlice α) : RustM usize :=
  pure (USize64.ofNat s.val.size)

@[spec]
def rust_primitives.sequence.seq_from_slice (α : Type) (s : RustSlice α) :
    RustM (rust_primitives.sequence.Seq α) :=
  pure s

@[spec]
def rust_primitives.slice.slice_split_at (α : Type) (s : RustSlice α) (mid : usize) :
    RustM (rust_primitives.hax.Tuple2 (RustSlice α) (RustSlice α)) :=
  if mid <= .ofNat s.val.size then
    pure ⟨⟨s.val.take mid.toNat, by grind⟩, ⟨s.val.drop mid.toNat, by grind⟩⟩
  else
    .fail .arrayOutOfBounds

def rust_primitives.slice.slice_slice
  (α : Type) (seq : RustSlice α) (s e : usize) : RustM (RustSlice α) :=
  if s ≤ e && e ≤ .ofNat seq.val.size then
    pure ⟨seq.val[s.toNat:e.toNat].toArray, by grind⟩
  else
    .fail .undef
