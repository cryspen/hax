/-
Hax Lean Backend - Cryspen

Core-model for Clone represented as a no-op
-/

import Hax.Rust_primitives

namespace core.clone

class Clone.AssociatedTypes (Self : Type) where

class Clone (Self : Type) [associatedTypes : outParam (Clone.AssociatedTypes (Self : Type))] where
  clone (Self) : (Self -> RustM Self)

@[reducible] instance Impl.AssociatedTypes (T : Type) : Clone.AssociatedTypes T where

instance Impl (T : Type) : Clone T where
  clone x := pure x

end core.clone
