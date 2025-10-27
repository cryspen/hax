/-
Hax Lean Backend - Cryspen

Core-model for [https://doc.rust-lang.org/core/result/index.html]:
Error handling with the Result type.
-/

import Hax.Lib
import Hax.Rust_primitives
import Hax.Core.Ops
import Hax.Core.Default
import Hax.Core.Panicking
open Rust_primitives.Hax
open Core.Ops
open Std.Do
set_option mvcgen.warning false

-- To avoid confusion with Hax Results
abbrev Hax_Result := Result

namespace Core.Result

inductive Result (α β : Type 0)
| Ok : α -> Result α β
| Err : β -> Result α β

def Impl.map
  (T : Type)
  (E : Type)
  (U : Type)
  (F : Type)
  [(Core.Ops.Function.FnOnce F T (Output := U))]
  (self : (Result T E))
  (op : F)
  : Hax_Result (Result U E)
  := do
  match self with
    | (Result.Ok t) =>
    (pure (Result.Ok (← (Core.Ops.Function.FnOnce.call_once op t))))
    | (Result.Err e)
      => (pure (Result.Err e))

def Impl.map_or
  (T : Type)
  (E : Type)
  (U : Type)
  (F : Type)
  [(Core.Ops.Function.FnOnce F T (Output := U))]
  (self : (Result T E))
  (default : U)
  (f : F)
  : Hax_Result U
  := do
  match self with
    | (Result.Ok t)
      => (Core.Ops.Function.FnOnce.call_once f t)
    | (Result.Err _e) => (pure default)

def Impl.map_or_else
  (T : Type)
  (E : Type)
  (U : Type)
  (D : Type)
  (F : Type)
  [(Core.Ops.Function.FnOnce F T (Output := U))]
  [(Core.Ops.Function.FnOnce D E (Output := U))]
  (self : (Result T E))
  (default : D)
  (f : F)
  : Hax_Result U
  := do
  match self with
    | (Result.Ok t)
      => (Core.Ops.Function.FnOnce.call_once f t)
    | (Result.Err e)
      => (Core.Ops.Function.FnOnce.call_once default e)

def Impl.map_err
  (T : Type)
  (E : Type)
  (F : Type)
  (O : Type)
  [(Core.Ops.Function.FnOnce O E (Output := F))]
  (self : (Result T E))
  (op : O)
  : Hax_Result (Result T F)
  := do
  match self with
    | (Result.Ok t) => (pure (Result.Ok t))
    | (Result.Err e) =>
        (pure (Result.Err
          (← (Core.Ops.Function.FnOnce.call_once op e))))

def Impl.is_ok
  (T : Type) (E : Type) (self : (Result T E))
  : Hax_Result Bool
  := do
  match self with
    | (Result.Ok _) => (pure true)
    | _ => (pure false)

def Impl.is_err
  (T : Type) (E : Type) (self : (Result T E))
  : Hax_Result Bool
  := do
  match self with
    | (Result.Ok _) => (pure false)
    | _ => (pure true)

def Impl.and_then
  (T : Type)
  (E : Type)
  (U : Type)
  (F : Type)
  [(Core.Ops.Function.FnOnce F T (Output := Result U E))]
  (self : (Result T E))
  (op : F)
  : Hax_Result (Result U E)
  := do
  match self with
    | (Result.Ok t)
      => (Core.Ops.Function.FnOnce.call_once op t)
    | (Result.Err e)
      => (pure (Result.Err e))

def Impl.unwrap
  (T : Type) (E : Type) (self : (Result T E))
  : Hax_Result T
  := do
  match self with
    | (Result.Ok t) => (pure t)
    | (Result.Err _)
      => (Core.Panicking.Internal.panic T Rust_primitives.Hax.Tuple0.mk)

@[spec]
theorem Impl.unwrap.spec {α β} (x: Result α β) v :
  x = Result.Ok v →
  ⦃ ⌜ True ⌝ ⦄
  (Impl.unwrap α β x)
  ⦃ ⇓ r => ⌜ r = v ⌝ ⦄
  := by
  intros
  mvcgen [Impl.unwrap] <;> try grind

def Impl.expect
  (T : Type) (E : Type) (self : (Result T E))
  (_msg : String)
  : Hax_Result T
  := do
  match self with
    | (Result.Ok t) => (pure t)
    | (Result.Err _)
      => (Core.Panicking.Internal.panic T Rust_primitives.Hax.Tuple0.mk)

end Core.Result
