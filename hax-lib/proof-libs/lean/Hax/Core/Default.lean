/-
Hax Lean Backend - Cryspen

Core-model for [https://doc.rust-lang.org/core/default/index.html]:
The Default trait for types with a default value.
-/

import Hax.Lib
import Hax.Rust_primitives
open Rust_primitives.Hax

namespace Core.Default

class Default (Self : Type) where
  default : Tuple0 -> RustM Self

end Core.Default
