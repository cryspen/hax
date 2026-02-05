import Hax.Rust_primitives.RustM
import Hax.Rust_primitives.Tuple

def Rust_primitives.Mem.replace (α : Type) (dst : α) (src : α) :
  RustM (Rust_primitives.Hax.Tuple2 α α) := pure ⟨src, dst⟩
