import Hax.rust_primitives.RustM
import Hax.rust_primitives.hax

def rust_primitives.mem.replace (α : Type) (dst : α) (src : α) :
  RustM (rust_primitives.hax.Tuple2 α α) := pure ⟨src, dst⟩
