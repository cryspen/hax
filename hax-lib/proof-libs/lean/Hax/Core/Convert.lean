/-
Hax Lean Backend - Cryspen
-/

import Hax.Lib
import Hax.Rust_primitives
import Hax.Core.Ops
import Hax.Core.Result
open Rust_primitives.Hax
open Core.Ops
open Std.Do

set_option mvcgen.warning false

namespace Core.Convert

class TryInto (Self: Type) (T: Type) {E: Type} where
  try_into (Self T) : Self → (RustM (Core.Result.Result T E))

instance {α : Type} {n : Nat} : TryInto (RustSlice α) (RustArray α n) (E := Core.Array.TryFromSliceError) where
  try_into a :=
   pure (
     if h: a.size = n then
       Core.Result.Result.Ok (a.toVector.cast h)
     else
       .Err Core.Array.TryFromSliceError.array.TryFromSliceError
     )

@[spec]
theorem TryInto.try_into.spec {α : Type} {n: Nat} (a: RustSlice α) :
  (h: a.size = n) →
  ⦃ ⌜ True ⌝ ⦄
  (TryInto.try_into (RustSlice α) (RustArray α n) (E := Core.Array.TryFromSliceError) a )
  ⦃ ⇓ r => ⌜ r = .Ok (a.toVector.cast h) ⌝ ⦄ := by
  intro h
  mvcgen [TryInto.try_into]
  grind

end Core.Convert
