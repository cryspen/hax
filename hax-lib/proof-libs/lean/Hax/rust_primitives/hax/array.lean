import Hax.rust_primitives.RustM
import Hax.rust_primitives.num
import Hax.rust_primitives.sequence

open Std.Do
set_option mvcgen.warning false

attribute [local grind! .] USize64.toNat_lt_size

/-

# Arrays

Rust arrays, are represented as Lean `Vector` (Lean Arrays of known size)

-/
section RustArray

structure RustArray (α : Type) (n : usize) where
  ofVec :: toVec : Vector α n.toNat

@[spec]
def rust_primitives.hax.monomorphized_update_at.update_at_usize {α n}
  (a : RustArray α n) (i : usize) (v : α) : RustM (RustArray α n) :=
  if h: i.toNat < a.toVec.size then
    pure (.ofVec (Vector.set a.toVec i.toNat v))
  else
    .fail (.arrayOutOfBounds)

@[spec]
def rust_primitives.hax.update_at {α n} (m : RustArray α n) (i : usize) (v : α) : RustM (RustArray α n) :=
  if i.toNat < n.toNat then
    pure (.ofVec (Vector.setIfInBounds m.toVec i.toNat v))
  else
    .fail (.arrayOutOfBounds)

@[spec]
def rust_primitives.hax.repeat
  {α int_type : Type}
  {n : usize} [ToNat int_type]
  (v:α) (size:int_type) : RustM (RustArray α n)
  :=
  if (n.toNat = ToNat.toNat size) then
    pure (.ofVec (Vector.replicate n.toNat v))
  else
    .fail Error.arrayOutOfBounds

@[spec]
def rust_primitives.unsize {α n} (a: RustArray α n) : RustM (rust_primitives.sequence.Seq α) :=
  pure ⟨a.toVec.toArray, by grind⟩

end RustArray
