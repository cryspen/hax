
import Hax.core_models.core_models

set_option mvcgen.warning false
open rust_primitives.hax
open Core.Ops
open Std.Do
namespace core_models.ops.function

instance {α β} : FnOnce.AssociatedTypes (α → RustM β) α where
  Output := β

instance {α β} : FnOnce.AssociatedTypes (α → RustM β) (Tuple1 α) where
  Output := β

instance {α β γ} : FnOnce.AssociatedTypes (α → β → RustM γ) (Tuple2 α β) where
  Output := γ

instance {α β} : FnOnce (α → RustM β) α where
  call_once f x := f x

instance {α β} : FnOnce (α → RustM β) (Tuple1 α) where
  call_once f x := f x._0

instance {α β γ : Type} : FnOnce (α → β → RustM γ) (Tuple2 α β) where
  call_once f x := f x._0 x._1


instance {α β} [FnOnce.AssociatedTypes (α → RustM β) α] : Fn.AssociatedTypes (α → RustM β) α where

instance {α β} [FnOnce.AssociatedTypes (α → RustM β) α] [FnOnce (α → RustM β) α] :
    Fn (α → RustM β) α where
  call f x := FnOnce.call_once _ _ f x

instance {α β} [FnOnce.AssociatedTypes (α → RustM β) (Tuple1 α)] :
  Fn.AssociatedTypes (α → RustM β) (Tuple1 α) where

instance {α β} [FnOnce.AssociatedTypes (α → RustM β) (Tuple1 α)] [FnOnce (α → RustM β) (Tuple1 α)] :
    Fn (α → RustM β) (Tuple1 α) where
  call f x := FnOnce.call_once _ _ f x

instance {α β γ} [FnOnce.AssociatedTypes (α → β → RustM γ) (Tuple2 α β)] :
  Fn.AssociatedTypes (α → β → RustM γ) (Tuple2 α β) where

instance {α β γ} [FnOnce.AssociatedTypes (α → β → RustM γ) (Tuple2 α β)] [FnOnce (α → β → RustM γ) (Tuple2 α β)] :
    Fn (α → β → RustM γ) (Tuple2 α β) where
  call f x := FnOnce.call_once _ _ f x

end core_models.ops.function
