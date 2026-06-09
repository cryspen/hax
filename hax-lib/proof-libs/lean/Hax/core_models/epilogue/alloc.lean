import Hax.core_models.core_models

open rust_primitives.hax

/-

# Vectors

Rust vectors are represented as Lean Arrays (variable size)

-/
section RustVectors

open rust_primitives.sequence

def alloc.alloc.Global : Type := Unit

abbrev alloc.vec.Vec (α: Type) (_Allocator:Type) : Type := Seq α

@[spec]
def alloc.vec.Impl.new (α: Type) (_:Tuple0) : RustM (alloc.vec.Vec α alloc.alloc.Global) :=
  pure ⟨(List.nil).toArray, by grind⟩

@[spec]
def alloc.vec.Impl_1.len (α: Type) (_Allocator: Type) (x: alloc.vec.Vec α alloc.alloc.Global) : RustM usize :=
  pure (.ofNat x.val.size)

@[spec]
def alloc.vec.Impl_2.extend_from_slice α (_Allocator: Type)
    (x: alloc.vec.Vec α alloc.alloc.Global) (y: Seq α) :
    RustM (alloc.vec.Vec α alloc.alloc.Global) :=
  if h : x.val.size + y.val.size < USize64.size then
    pure ⟨x.val.append y.val, by simp [h]⟩
  else
    .fail .maximumSizeExceeded

@[spec]
def alloc.slice.Impl.to_vec α (a: rust_primitives.sequence.Seq α) :
    RustM (alloc.vec.Vec α alloc.alloc.Global) :=
  pure a

end RustVectors
