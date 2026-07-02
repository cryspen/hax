import Aeneas

/-!

# Types Prologue

This file contains workarounds required to be present before `Types.lean` runs. The file
`Types.lean` contains the types automatically generated from our Rust implementation of core.
Since it's automatically generated, we cannot move this material there.

-/

open Aeneas.Std

namespace CoreModels.core

/-! ## Function closures -/

namespace ops.function
structure FnOnce (Self : Type) (Args : Type) (Self_Output : Type) where
  call_once : Self → Args → Result Self_Output

structure FnMut (Self : Type) (Args : Type) (Self_Clause0_Output : Type) where
  FnOnceInst : FnOnce Self Args Self_Clause0_Output
  call_mut : Self → Args → Result (Self_Clause0_Output × Self)

structure Fn (Self : Type) (Args : Type) (Self_Clause0_Output : Type) where
  FnMutInst : FnMut Self Args Self_Clause0_Output
  call : Self → Args → Result Self_Clause0_Output
end ops.function

def marker.PhantomData (A : Type) := Unit
def marker.PhantomData.mk: Unit := ()

/-! ## Option

Rust's `Option` aliased to Lean's built-in

-/

namespace option

abbrev Option := _root_.Option
@[match_pattern] abbrev Option.Some {T} (x : T) : Option T := _root_.Option.some x
@[match_pattern] abbrev Option.None {T} : Option T := _root_.Option.none

end option

inductive cmp.Ordering where
| Less : cmp.Ordering
| Equal : cmp.Ordering
| Greater : cmp.Ordering


/-! ## Rust's `Result` enum -/
namespace result

inductive Result (T : Type) (E : Type) where
| Ok : T → Result T E
| Err : E → Result T E

def Result.ok {T E : Type} (r : Result T E) : Aeneas.Std.Result (_root_.Option T) :=
  match r with
  | Result.Ok t  => Aeneas.Std.Result.ok (some t)
  | Result.Err _ => Aeneas.Std.Result.ok none

/-- `Result<T, E>::err(self) -> Option<E>`. Same `abbrev` rationale. -/
def Result.err {T E : Type} (r : Result T E) : Aeneas.Std.Result (_root_.Option E) :=
  match r with
  | Result.Ok _  => Aeneas.Std.Result.ok none
  | Result.Err e => Aeneas.Std.Result.ok (some e)

/-- `Result<T, E>::is_ok(&self) -> bool`. -/
def Result.is_ok {T E : Type} (r : Result T E) : Aeneas.Std.Result Bool :=
  match r with
  | Result.Ok _  => Aeneas.Std.Result.ok true
  | Result.Err _ => Aeneas.Std.Result.ok false

/-- `Result<T, E>::is_err(&self) -> bool`. -/
def Result.is_err {T E : Type} (r : Result T E) : Aeneas.Std.Result Bool :=
  match r with
  | Result.Ok _  => Aeneas.Std.Result.ok false
  | Result.Err _ => Aeneas.Std.Result.ok true
end result

end CoreModels.core

/-! ## Hax lib -/
namespace hax_lib

@[reducible] def int.Int := _root_.Int

end hax_lib
