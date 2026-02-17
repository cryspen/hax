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

abbrev RustArray (α : Type) (n : usize) := Vector α n.toNat

def rust_primitives.hax.monomorphized_update_at.update_at_usize {α n}
  (a : Vector α n) (i : usize) (v : α) : RustM (Vector α n) :=
  if h: i.toNat < a.size then
    pure ( Vector.set a i.toNat v )
  else
    .fail (.arrayOutOfBounds)

@[spec]
theorem rust_primitives.hax.monomorphized_update_at.update_at_usize.spec
  {α n} (a: Vector α n) (i:usize) (v:α) (h: i.toNat < a.size) :
  ⦃ ⌜ True ⌝ ⦄
  (rust_primitives.hax.monomorphized_update_at.update_at_usize a i v)
  ⦃ ⇓ r => ⌜ r = Vector.set a i.toNat v ⌝ ⦄ := by
  mvcgen [rust_primitives.hax.monomorphized_update_at.update_at_usize]


@[spec]
def rust_primitives.hax.update_at {α n} (m : Vector α n) (i : usize) (v : α) : RustM (Vector α n) :=
  if i.toNat < n then
    pure ( Vector.setIfInBounds m i.toNat v)
  else
    .fail (.arrayOutOfBounds)

@[spec]
def rust_primitives.hax.repeat
  {α int_type: Type}
  {n: Nat} [ToNat int_type]
  (v:α) (size:int_type) : RustM (Vector α n)
  :=
  if (n = ToNat.toNat size) then
    pure (Vector.replicate n v)
  else
    .fail Error.arrayOutOfBounds

@[spec]
def rust_primitives.unsize {α n} (a: RustArray α n) : RustM (rust_primitives.sequence.Seq α) :=
  pure ⟨a.toArray, by grind⟩

end RustArray
