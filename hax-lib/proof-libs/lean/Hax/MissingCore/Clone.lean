/-
Hax Lean Backend - Cryspen

Core-model for Clone represented as a no-op
-/

import Hax.Rust_primitives

namespace Core.Clone

class Clone (Self : Type) where

def Clone.clone {Self: Type} : Self -> RustM Self :=
  fun x => pure x

end Core.Clone
