
import Hax.Lib
import Hax.Rust_primitives
import Hax.Core.Ops
import Hax.Core.Default
open Rust_primitives.Hax
open Core.Ops

namespace Core.Panicking.Internal

def panic (T : Type) (_ : Rust_primitives.Hax.Tuple0)
  : RustM T
  := do .fail .panic

end Core.Panicking.Internal
