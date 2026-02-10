import Hax.Rust_primitives.RustM
import Hax.Rust_primitives.Tuple
import Hax.Rust_primitives.Num

open rust_primitives.hax

/-

# Vectors

Rust vectors are represented as Lean Arrays (variable size)

-/
section RustVectors

abbrev RustSlice := Array
abbrev RustVector := Array

def alloc.alloc.Global : Type := Unit

abbrev alloc.Vec.Vec (α: Type) (_Allocator:Type) : Type := Array α

def alloc.Vec.Impl.new (α: Type) (_:Tuple0) : RustM (alloc.Vec.Vec α alloc.alloc.Global) :=
  pure ((List.nil).toArray)

def alloc.Vec.Impl_1.len (α: Type) (_Allocator: Type) (x: alloc.Vec.Vec α alloc.alloc.Global) : RustM usize :=
  pure x.size

def alloc.Vec.Impl_2.extend_from_slice α (_Allocator: Type) (x: alloc.Vec.Vec α alloc.alloc.Global) (y: Array α)
  : RustM (alloc.Vec.Vec α alloc.alloc.Global):=
  pure (x.append y)

def alloc.Slice.Impl.to_vec α (a:  Array α) : RustM (alloc.Vec.Vec α alloc.alloc.Global) :=
  pure a

-- For
instance {α n} : Coe (Array α) (RustM (Vector α n)) where
  coe x :=
    if h: x.size = n then by
      rw [←h]
      apply pure
      apply (Array.toVector x)
    else .fail (.arrayOutOfBounds)

end RustVectors
