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

/- Warning : this function has been specialized, it should be turned into a typeclass -/
def Core.Convert.TryInto.try_into {α n} (a: Array α) :
   Result (Core.Result.Result (Vector α n) Core.Array.TryFromSliceError) :=
   pure (
     if h: a.size = n then
       Core.Result.Result.Ok (a.toVector.cast h)
     else
       .Err Core.Array.TryFromSliceError.array.TryFromSliceError
     )

@[spec]
theorem Core.Convert.TryInto.try_into.spec {α n} (a: Array α) :
  (h: a.size = n) →
  ⦃ ⌜ True ⌝ ⦄
  ( Core.Convert.TryInto.try_into a)
  ⦃ ⇓ r => ⌜ r = .Ok (a.toVector.cast h) ⌝ ⦄ := by
  intro h
  mvcgen [Core.Result.Impl.unwrap.spec, Core.Convert.TryInto.try_into]
  grind
