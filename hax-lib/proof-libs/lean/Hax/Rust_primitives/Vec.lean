import Hax.Rust_primitives.RustM
import Hax.Rust_primitives.Tuple
import Hax.Rust_primitives.Num

open Rust_primitives.Hax

/-

# Vectors

Rust vectors are represented as Lean Arrays (variable size)

-/
section RustVectors

abbrev RustSlice := Array
abbrev RustVector := Array

def Alloc.Alloc.Global : Type := Unit

abbrev Alloc.Vec.Vec (α: Type) (_Allocator:Type) : Type := Array α

def Alloc.Vec.Impl.new (α: Type) (_:Tuple0) : RustM (Alloc.Vec.Vec α Alloc.Alloc.Global) :=
  pure ((List.nil).toArray)

def Alloc.Vec.Impl_1.len (α: Type) (_Allocator: Type) (x: Alloc.Vec.Vec α Alloc.Alloc.Global) : RustM usize :=
  pure x.size

def Alloc.Vec.Impl_2.extend_from_slice α (_Allocator: Type) (x: Alloc.Vec.Vec α Alloc.Alloc.Global) (y: Array α)
  : RustM (Alloc.Vec.Vec α Alloc.Alloc.Global):=
  pure (x.append y)

def Alloc.Slice.Impl.to_vec α (a:  Array α) : RustM (Alloc.Vec.Vec α Alloc.Alloc.Global) :=
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
