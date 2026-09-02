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
  call_once : Self → Args → RustM Self_Output

structure FnMut (Self : Type) (Args : Type) (Self_Clause0_Output : Type) where
  FnOnceInst : FnOnce Self Args Self_Clause0_Output
  call_mut : Self → Args → RustM (Self_Clause0_Output × Self)

structure Fn (Self : Type) (Args : Type) (Self_Clause0_Output : Type) where
  FnMutInst : FnMut Self Args Self_Clause0_Output
  call : Self → Args → RustM Self_Clause0_Output
end ops.function

def marker.PhantomData (_ : Type) := Unit
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

def Result.ok {T E : Type} (r : Result T E) : Aeneas.Std.RustM (_root_.Option T) :=
  match r with
  | Result.Ok t  => Aeneas.Std.RustM.ok (some t)
  | Result.Err _ => Aeneas.Std.RustM.ok none

/-- `Result<T, E>::err(self) -> Option<E>`. Same `abbrev` rationale. -/
def Result.err {T E : Type} (r : Result T E) : Aeneas.Std.RustM (_root_.Option E) :=
  match r with
  | Result.Ok _  => Aeneas.Std.RustM.ok none
  | Result.Err e => Aeneas.Std.RustM.ok (some e)

/-- `Result<T, E>::is_ok(&self) -> bool`. -/
def Result.is_ok {T E : Type} (r : Result T E) : Aeneas.Std.RustM Bool :=
  match r with
  | Result.Ok _  => Aeneas.Std.RustM.ok true
  | Result.Err _ => Aeneas.Std.RustM.ok false

/-- `Result<T, E>::is_err(&self) -> bool`. -/
def Result.is_err {T E : Type} (r : Result T E) : Aeneas.Std.RustM Bool :=
  match r with
  | Result.Ok _  => Aeneas.Std.RustM.ok false
  | Result.Err _ => Aeneas.Std.RustM.ok true
end result

/-! ## `core::slice::IterMut` — mutable-element slice iterator

Modelled as Aeneas.Std does (`SliceIter.lean`): an opaque `{slice, index}`, NOT an
`Iterator` instance — a `&mut`-yielding iterator's `next` must return a 3-tuple
`(Option T) × Self × back-prop-fn` (the yielded `&mut T`'s write-back), which the
`Iterator` trait's 2-tuple `next` can't hold. Its specialised `next` (in the
epilogue) is what a downstream extraction calls directly. -/
namespace slice.iter
structure IterMut (T : Type) where
  slice : Slice T
  i : Nat := 0
end slice.iter

end CoreModels.core

/-! ## Hax lib -/
namespace hax_lib

@[reducible] def int.Int := _root_.Int

end hax_lib
