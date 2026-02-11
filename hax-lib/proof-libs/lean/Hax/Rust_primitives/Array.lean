
import Hax.Rust_primitives.RustM
import Hax.Rust_primitives.Num

open Std.Do

set_option mvcgen.warning false

/-

# Arrays

Rust arrays, are represented as Lean `Vector` (Lean Arrays of known size)

-/
section RustArray


abbrev RustArray := Vector

def rust_primitives.hax.monomorphized_update_at.update_at_usize {α n}
  (a: Vector α n) (i:Nat) (v:α) : RustM (Vector α n) :=
  if h: i < a.size then
    pure ( Vector.set a i v )
  else
    .fail (.arrayOutOfBounds)

@[spec]
theorem rust_primitives.hax.monomorphized_update_at.update_at_usize.spec
  {α n} (a: Vector α n) (i:Nat) (v:α) (h: i < a.size) :
  ⦃ ⌜ True ⌝ ⦄
  (rust_primitives.hax.monomorphized_update_at.update_at_usize a i v)
  ⦃ ⇓ r => ⌜ r = Vector.set a i v ⌝ ⦄ := by
  mvcgen [rust_primitives.hax.monomorphized_update_at.update_at_usize]


@[spec]
def rust_primitives.hax.update_at {α n} (m : Vector α n) (i : Nat) (v : α) : RustM (Vector α n) :=
  if i < n then
    pure ( Vector.setIfInBounds m i v)
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
def rust_primitives.unsize {α n} (a: Vector α n) : RustM (Array α) :=
  pure (a.toArray)

end RustArray
