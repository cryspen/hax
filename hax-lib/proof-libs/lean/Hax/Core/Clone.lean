/-
Hax Lean Backend - Cryspen

Core-model for Clone represented as a no-op
-/

import Hax.Lib
import Hax.Rust_primitives
open Rust_primitives.Hax

-- TODO: Why is there `Core_models.Clone` and `Core.Clone`?

namespace Core_models.Clone

class Clone.AssociatedTypes (Self : Type) where

class Clone
    (Self : Type)
    [associatedTypes : outParam (Clone.AssociatedTypes (Self : Type))] where
  clone : Self -> RustM Self

end Core_models.Clone

namespace Core.Clone

class Clone.AssociatedTypes (Self : Type) where

class Clone
    (Self : Type)
    [associatedTypes : outParam (Clone.AssociatedTypes (Self : Type))] where
  clone : Self -> RustM Self

end Core.Clone
