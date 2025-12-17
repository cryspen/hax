/-
Hax Lean Backend - Cryspen

Core-model for Clone represented as a no-op
-/

import Hax.Lib
import Hax.Rust_primitives
open Rust_primitives.Hax

namespace Core.Clone

class Clone.AssociatedTypes (Self : Type) where

class Clone
  (Self : Type)
  [associatedTypes : outParam (Clone.AssociatedTypes (Self :
      Type))]

def Clone.clone {Self: Type} : Self -> RustM Self :=
  fun x => pure x

end Core.Clone
