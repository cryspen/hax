import Hax.rust_primitives.RustM
import Hax.rust_primitives.hax

def rust_primitives.mem.copy (α : Type) (a : α) : RustM α := pure a
