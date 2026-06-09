/-
Hax Lean Backend - Cryspen

Core-model for Clone represented as a no-op
-/

import Hax.rust_primitives

namespace core.clone

class Clone (Self : Type) where

def Clone.clone {Self: Type} : Self -> RustM Self :=
  fun x => pure x

end core.clone
