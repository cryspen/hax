import Hax.core_models.core_models

open rust_primitives.hax

/-

# Vectors

Rust vectors are represented as Lean Arrays (variable size)

-/
section RustVectors

def alloc.alloc.Global : Type := Unit

abbrev alloc.vec.Vec (α: Type) (_Allocator:Type) : Type := Array α

def alloc.vec.Impl.new (α: Type) (_:Tuple0) : RustM (alloc.vec.Vec α alloc.alloc.Global) :=
  pure ((List.nil).toArray)

def alloc.vec.Impl_1.len (α: Type) (_Allocator: Type) (x: alloc.vec.Vec α alloc.alloc.Global) : RustM usize :=
  pure x.size

def alloc.vec.Impl_2.extend_from_slice α (_Allocator: Type) (x: alloc.vec.Vec α alloc.alloc.Global) (y: Array α)
  : RustM (alloc.vec.Vec α alloc.alloc.Global):=
  pure (x.append y)

def alloc.slice.Impl.to_vec α (a:  Array α) : RustM (alloc.vec.Vec α alloc.alloc.Global) :=
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
