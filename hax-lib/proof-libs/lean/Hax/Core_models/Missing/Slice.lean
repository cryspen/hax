import Hax.Core_models.Extracted

/-

# Slices

Rust slices are represented as Lean Arrays (variable size)

-/

@[simp, spec]
def Core_models.Slice.Impl.len α (a: Array α) : RustM usize := pure a.size

def Core_models.Slice.Impl.is_empty α (a : Array α) : RustM Bool := do
  let n ← Core_models.Slice.Impl.len α a
  pure (n == 0)
