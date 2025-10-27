/-
Hax Lean Backend - Cryspen

Core-model for [https://doc.rust-lang.org/src/core/ops/function.rs.html]:
-/

import Hax.Lib
import Hax.Rust_primitives
open Rust_primitives.Hax

namespace Core.Ops.Function

class FnOnce (Self Args : Type) {Output: Type} where
  call_once : Self -> Args -> Result Output
  Output : Type := Output

class Fn (Self Args : Type) {Output: Type} where
  [_constr_10219838627318688691 : (FnOnce Self Args (Output := Output))]
  call : Self -> Args -> Result Output

instance {α β} : FnOnce (α → Result β) α (Output := β) where
  Output := β
  call_once f x := f x

instance {α β} : FnOnce (α → Result β) (Tuple1 α) (Output := β) where
  Output := β
  call_once f x := f x._0

instance {α β γ : Type} : FnOnce (α → β → Result γ) (Tuple2 α β) (Output := γ) where
  Output := γ
  call_once f x := f x._0 x._1

instance {α β} : Fn (α → Result β) α (Output := β) where
  call f x := (FnOnce.call_once) f x

instance {α β} : Fn (α → Result β) (Tuple1 α) (Output := β) where
  call f x := (FnOnce.call_once) f x

instance {α β γ} : Fn (α → β → Result γ) (Tuple2 α β) (Output := γ) where
  call f x := (FnOnce.call_once) f x
