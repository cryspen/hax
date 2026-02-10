import Hax.Rust_primitives.RustM
import Hax.Rust_primitives.Tuple

def rust_primitives.Mem.replace (α : Type) (dst : α) (src : α) :
  RustM (rust_primitives.hax.Tuple2 α α) := pure ⟨src, dst⟩
