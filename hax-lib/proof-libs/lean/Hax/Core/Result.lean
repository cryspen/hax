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

inductive Result α β
| Ok : α -> Result α β
| Err : β -> Result α β

instance {β : Type} : Monad (fun α => Result α β) where
  pure x := .Ok x
  bind {α α'} x (f: α -> Result α' β) := match x with
  | .Ok v => f v
  | .Err e => .Err e

/-- Rust unwrapping, panics if `x` is not `result.Result.ok _` -/
def Impl.unwrap (α: Type) (β:Type) (x: Result α β) :=
  match x with
  | .Err _ => Result.fail .panic
  | .Ok v => pure v

@[spec]
theorem Impl.unwrap.spec {α β} (x: Result α β) v :
  x = Result.Ok v →
  ⦃ ⌜ True ⌝ ⦄
  (Impl.unwrap α β x)
  ⦃ ⇓ r => ⌜ r = v ⌝ ⦄
  := by
  intros
  mvcgen [Impl.unwrap] <;> try grind

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

def Core.Result.Impl.map_or
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

def Core.Result.Impl.map_or_else
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

def Core.Result.Impl.map_err
  (T : Type)
  (E : Type)
  (O : Type)
  (F : Type)
  [(Core.Ops.Function.FnOnce O E (Output := F))]
  (self : (Result T E))
  (op : O)
  : Hax_Result (Result T F)
  := do
  match self with
    | (Result.Ok t)
      => (pure (Result.Ok t))
    | (Result.Err e)
      =>
        (pure (Result.Err
          (← (Core.Ops.Function.FnOnce.call_once op e))))

def Core.Result.Impl.is_ok
  (T : Type) (E : Type) (self : (Result T E))
  : Hax_Result Bool
  := do
  match self with
    | (Result.Ok _) => (pure true)
    | _ => (pure false)

def Core.Result.Impl.and_then
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

def Core.Result.Impl.unwrap._.requires
  (T : Type) (E : Type) (self_ : (Result T E))
  : Hax_Result Bool
  := do
  (Core.Result.Impl.is_ok T E self_)

def Core.Result.Impl.unwrap
  (T : Type) (E : Type) (self : (Result T E))
  : Hax_Result T
  := do
  match self with
    | (Result.Ok t) => (pure t)
    | (Result.Err _)
      => (Core.Panicking.Internal.panic T Rust_primitives.Hax.Tuple0.mk)

def Core.Result.Impl.expect._.requires
  (T : Type) (E : Type) (self_ : (Result T E))
  (_msg : String)
  : Hax_Result Bool
  := do
  (Core.Result.Impl.is_ok T E self_)

def Core.Result.Impl.expect
  (T : Type) (E : Type) (self : (Result T E))
  (_msg : String)
  : Hax_Result T
  := do
  match self with
    | (Result.Ok t) => (pure t)
    | (Result.Err _)
      => (Core.Panicking.Internal.panic T Rust_primitives.Hax.Tuple0.mk)

end Core.Result
