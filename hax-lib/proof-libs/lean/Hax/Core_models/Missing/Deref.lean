import Hax.Core_models.Extracted

def Core_models.Ops.Deref.Deref.deref {α Allocator} (_ : Type) (v: Alloc.Vec.Vec α Allocator)
  : RustM (Array α)
  := pure v
