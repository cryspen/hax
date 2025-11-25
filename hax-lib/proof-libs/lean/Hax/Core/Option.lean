/-
Hax Lean Backend - Cryspen

Core-model for [https://doc.rust-lang.org/core/option/index.html]:
Optional values.
-/

import Hax.Lib
import Hax.Rust_primitives
import Hax.Core.Ops
import Hax.Core.Default
import Hax.Core.Panicking
import Hax.Core.Result
open Rust_primitives.Hax
open Core.Ops
open Core.Result
open Std.Do
set_option mvcgen.warning false

namespace Core.Option

inductive Option (T : Type) : Type
| Some : T -> Option T
| None : Option T

def Impl.is_some_and
  (T : Type) (F : Type) [(Function.FnOnce (Output := Bool) F T)] (self :
  (Option T))
  (f : F)
  : RustM Bool
  := do
  match self with
    | (Option.None ) => (pure false)
    | (Option.Some x)
      => (Function.FnOnce.call_once f x)

def Impl.is_none_or
  (T : Type) (F : Type) [(Function.FnOnce (Output := Bool) F T)] (self :
  (Option T))
  (f : F)
  : RustM Bool
  := do
  match self with
    | (Option.None ) => (pure true)
    | (Option.Some x)
      => (Function.FnOnce.call_once f x)

def Impl.as_ref
  (T : Type) (self : (Option T))
  : RustM (Option T)
  := do
  match self with
    | (Option.Some x)
      => (pure (Option.Some x))
    | (Option.None ) => (pure Option.None)

def Impl.unwrap_or
  (T : Type) (self : (Option T))
  (default : T)
  : RustM T
  := do
  match self with
    | (Option.Some x) => (pure x)
    | (Option.None ) => (pure default)

def Impl.unwrap_or_else
  (T : Type)
  (F : Type)
  [(Function.FnOnce F Rust_primitives.Hax.Tuple0 (Output := T))]
  (self : (Option T))
  (f : F)
  : RustM T
  := do
  match self with
    | (Option.Some x) => (pure x)
    | (Option.None ) => (Function.FnOnce.call_once f Rust_primitives.Hax.Tuple0.mk)

def Impl.unwrap_or_default
  (T : Type) [(Core.Default.Default T)] (self :
  (Option T))
  : RustM T
  := do
  match self with
    | (Option.Some x) => (pure x)
    | (Option.None ) => (Core.Default.Default.default Rust_primitives.Hax.Tuple0.mk)

def Impl.map
  (T : Type)
  (U : Type)
  (F : Type)
  [(Function.FnOnce F T (Output := U))]
  (self : (Option T))
  (f : F)
  : RustM (Option U)
  := do
  match self with
    | (Option.Some x) => (pure (Option.Some (← (Function.FnOnce.call_once f x))))
    | (Option.None ) => (pure Option.None)

def Impl.map_or
  (T : Type)
  (U : Type)
  (F : Type)
  [(Function.FnOnce F T (Output := U))]
  (self : (Option T))
  (default : U)
  (f : F)
  : RustM U
  := do
  match self with
    | (Option.Some t) => (Function.FnOnce.call_once f t)
    | (Option.None ) => (pure default)

def Impl.map_or_else
  (T : Type)
  (U : Type)
  (D : Type)
  (F : Type)
  [(Function.FnOnce F T (Output := U))]
  [(Function.FnOnce D Rust_primitives.Hax.Tuple0 (Output := U))]
  (self : (Option T))
  (default : D)
  (f : F)
  : RustM U
  := do
  match self with
    | (Option.Some t) => (Function.FnOnce.call_once f t)
    | (Option.None ) => (Function.FnOnce.call_once default Rust_primitives.Hax.Tuple0.mk)

def Impl.map_or_default
  (T : Type)
  (U : Type)
  (F : Type)
  [(Function.FnOnce F T (Output := U))]
  [(Core.Default.Default U)]
  (self : (Option T))
  (f : F)
  : RustM U
  := do
  match self with
    | (Option.Some t)
      => (Function.FnOnce.call_once f t)
    | (Option.None )
      => (Core.Default.Default.default Rust_primitives.Hax.Tuple0.mk)


def Impl.ok_or
  (T : Type) (E : Type) (self : (Option T))
  (err : E)
  : RustM (Result T E)
  := do
  match self with
    | (Option.Some v)
      => (pure (Result.Ok v))
    | (Option.None )
      => (pure (Result.Err err))

def Impl.ok_or_else
  (T : Type)
  (E : Type)
  (F : Type)
  [(Function.FnOnce F Rust_primitives.Hax.Tuple0 (Output := E))]
  (self : (Option T))
  (err : F)
  : RustM (Result T E)
  := do
  match self with
    | (Option.Some v)
      => (pure (Result.Ok v))
    | (Option.None )
      =>
        (pure (Result.Err
          (← (Function.FnOnce.call_once
            err
            Rust_primitives.Hax.Tuple0.mk))))

def Impl.and_then
  (T : Type)
  (U : Type)
  (F : Type)
  [(Function.FnOnce F T (Output := Option U))]
  (self : (Option T))
  (f : F)
  : RustM (Option U)
  := do
  match self with
    | (Option.Some x)
      => (Function.FnOnce.call_once f x)
    | (Option.None ) => (pure Option.None)

def Impl.take
  (T : Type) (self : (Option T))
  : RustM
  (Rust_primitives.Hax.Tuple2
    (Option T)
    (Option T))
  := do
  (pure (Rust_primitives.Hax.Tuple2.mk Option.None self))

def Impl.is_some
  (T : Type) (self : (Option T))
  : RustM Bool
  := do
  match self with
    | (Option.Some _) => (pure true)
    | _ => (pure false)

@[spec]
def Impl.is_some.spec
  (T : Type) (x : (Option T)) :
  ⦃ ⌜ True ⌝ ⦄
  (Impl.is_some T x)
  ⦃ ⇓ r =>
    ⌜ r = match x with
    | Option.Some _ => true
    | Option.None => false ⌝ ⦄ := by
    mvcgen [Impl.is_some] <;> grind

def Impl.is_none
  (T : Type) (self : (Option T))
  : RustM Bool
  := do
  match self with
    | (Option.Some _) => (pure false)
    | _ => (pure true)

def Impl.expect
  (T : Type) (self : (Option T))
  (_msg : String)
  : RustM T
  := do
  match self with
    | (Option.Some val) => (pure val)
    | (Option.None )
      => (Core.Panicking.Internal.panic T Rust_primitives.Hax.Tuple0.mk)

def Impl.unwrap._.requires
  (T : Type) (self_ : (Option T))
  : RustM Bool
  := do
  (Impl.is_some T self_)

def Impl.unwrap
  (T : Type) (self : (Option T))
  : RustM T
  := do
  match self with
    | (Option.Some val) => (pure val)
    | (Option.None )
      => (Core.Panicking.Internal.panic T Rust_primitives.Hax.Tuple0.mk)
