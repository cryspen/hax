import Hax.Rust_primitives.RustM
import Hax.Rust_primitives.Vec
import Hax.Rust_primitives.Array

def Rust_primitives.Slice.array_as_slice (α : Type) (n : usize) : RustArray α n → RustM (RustSlice α) :=
  fun x => pure (Vector.toArray x)

def Rust_primitives.Slice.array_map (α : Type) (β : Type) (n : usize) (_ : Type)
    (a : RustArray α n) (f : α -> RustM β) : RustM (RustArray β n) :=
  a.mapM f

def Rust_primitives.Slice.array_from_fn (α : Type) (n : usize) (_ : Type)
    (f : usize -> RustM α) : RustM (RustArray α n) :=
  (Vector.range n).mapM fun i => f (USize64.ofNat i)
