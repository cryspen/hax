
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace new_tests.rustc_coverage__branch__match_arms

inductive Enum : Type
| A : u32 -> Enum
| B : u32 -> Enum
| C : u32 -> Enum
| D : u32 -> Enum

@[instance] opaque Impl.AssociatedTypes :
  core_models.clone.Clone.AssociatedTypes Enum :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl :
  core_models.clone.Clone Enum :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1.AssociatedTypes :
  core_models.marker.Copy.AssociatedTypes Enum :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1 :
  core_models.marker.Copy Enum :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2.AssociatedTypes :
  core_models.fmt.Debug.AssociatedTypes Enum :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2 :
  core_models.fmt.Debug Enum :=
  by constructor <;> exact Inhabited.default

def consume (T : Type) (x : T) : RustM rust_primitives.hax.Tuple0 := do
  let _ ← (core_models.hint.black_box T x);
  (pure rust_primitives.hax.Tuple0.mk)

--  @fail(extraction): proverif(HAX0008)
def match_arms (value : Enum) : RustM rust_primitives.hax.Tuple0 := do
  let _ ←
    (rust_primitives.hax.folds.fold_range
      (0 : i32)
      (1 : i32)
      (fun _ _ => (do (pure true) : RustM Bool))
      rust_primitives.hax.Tuple0.mk
      (fun _ _ =>
        (do
        (pure rust_primitives.hax.Tuple0.mk) :
        RustM rust_primitives.hax.Tuple0)));
  let _ ←
    match value with
      | (Enum.D  d) => (consume u32 d)
      | (Enum.C  c) => (consume u32 c)
      | (Enum.B  b) => (consume u32 b)
      | (Enum.A  a) => (consume u32 a);
  let _ ← (consume i32 (0 : i32));
  (pure rust_primitives.hax.Tuple0.mk)

--  @fail(extraction): proverif(HAX0008)
def or_patterns (value : Enum) : RustM rust_primitives.hax.Tuple0 := do
  let _ ←
    (rust_primitives.hax.folds.fold_range
      (0 : i32)
      (1 : i32)
      (fun _ _ => (do (pure true) : RustM Bool))
      rust_primitives.hax.Tuple0.mk
      (fun _ _ =>
        (do
        (pure rust_primitives.hax.Tuple0.mk) :
        RustM rust_primitives.hax.Tuple0)));
  let _ ←
    match value with
      | (Enum.D  x) | (Enum.C  x) => (consume u32 x)
      | (Enum.B  y) | (Enum.A  y) => (consume u32 y);
  let _ ← (consume i32 (0 : i32));
  (pure rust_primitives.hax.Tuple0.mk)

--  @fail(extraction): proverif(HAX0008, HAX0008)
def guards (value : Enum) (cond : Bool) : RustM rust_primitives.hax.Tuple0 := do
  let _ ←
    (rust_primitives.hax.folds.fold_range
      (0 : i32)
      (1 : i32)
      (fun _ _ => (do (pure true) : RustM Bool))
      rust_primitives.hax.Tuple0.mk
      (fun _ _ =>
        (do
        (pure rust_primitives.hax.Tuple0.mk) :
        RustM rust_primitives.hax.Tuple0)));
  let _ ←
    match
      (← match value with
        | (Enum.D  d) =>
          match cond with
            | true =>
              (pure (core_models.option.Option.Some (← (consume u32 d))))
            | _ => (pure core_models.option.Option.None)
        | _ => (pure core_models.option.Option.None))
    with
      | (core_models.option.Option.Some  x) => (pure x)
      | (core_models.option.Option.None ) =>
        match
          (← match value with
            | (Enum.C  c) =>
              match cond with
                | true =>
                  (pure (core_models.option.Option.Some (← (consume u32 c))))
                | _ => (pure core_models.option.Option.None)
            | _ => (pure core_models.option.Option.None))
        with
          | (core_models.option.Option.Some  x) => (pure x)
          | (core_models.option.Option.None ) =>
            match
              (← match value with
                | (Enum.B  b) =>
                  match cond with
                    | true =>
                      (pure (core_models.option.Option.Some
                        (← (consume u32 b))))
                    | _ => (pure core_models.option.Option.None)
                | _ => (pure core_models.option.Option.None))
            with
              | (core_models.option.Option.Some  x) => (pure x)
              | (core_models.option.Option.None ) =>
                match
                  (← match value with
                    | (Enum.A  a) =>
                      match cond with
                        | true =>
                          (pure (core_models.option.Option.Some
                            (← (consume u32 a))))
                        | _ => (pure core_models.option.Option.None)
                    | _ => (pure core_models.option.Option.None))
                with
                  | (core_models.option.Option.Some  x) => (pure x)
                  | (core_models.option.Option.None ) =>
                    (consume i32 (0 : i32));
  let _ ← (consume i32 (0 : i32));
  (pure rust_primitives.hax.Tuple0.mk)

--  @fail(extraction): proverif(HAX0008)
def main.call_everything (e : Enum) :
    RustM
    (rust_primitives.hax.Tuple2
      rust_primitives.hax.Tuple0
      rust_primitives.hax.Tuple0)
    := do
  let _ ← (match_arms e);
  let _ ← (or_patterns e);
  (pure (rust_primitives.hax.Tuple2.mk
    (← (core_models.iter.traits.iterator.Iterator.fold
      (← (core_models.iter.traits.collect.IntoIterator.into_iter
        (RustArray Bool 3) #v[false, false, true]))
      rust_primitives.hax.Tuple0.mk
      (fun _ cond => (do (guards e cond) : RustM rust_primitives.hax.Tuple0))))
    rust_primitives.hax.Tuple0.mk))

--  @fail(extraction): proverif(HAX0008)
--  @fail(extraction): proverif(HAX0008, HAX0008)
def main (_ : rust_primitives.hax.Tuple0) :
    RustM
    (rust_primitives.hax.Tuple2
      rust_primitives.hax.Tuple0
      rust_primitives.hax.Tuple0)
    := do
  let _ ← (main.call_everything (Enum.A (0 : u32)));
  let _ ←
    (rust_primitives.hax.folds.fold_range
      (0 : u32)
      (2 : u32)
      (fun _ _ => (do (pure true) : RustM Bool))
      rust_primitives.hax.Tuple0.mk
      (fun _ b =>
        (do
        (main.call_everything (Enum.B b)) : RustM rust_primitives.hax.Tuple0)));
  let _ ←
    (rust_primitives.hax.folds.fold_range
      (0 : u32)
      (4 : u32)
      (fun _ _ => (do (pure true) : RustM Bool))
      rust_primitives.hax.Tuple0.mk
      (fun _ c =>
        (do
        (main.call_everything (Enum.C c)) : RustM rust_primitives.hax.Tuple0)));
  (pure (rust_primitives.hax.Tuple2.mk
    (← (rust_primitives.hax.folds.fold_range
      (0 : u32)
      (8 : u32)
      (fun _ _ => (do (pure true) : RustM Bool))
      rust_primitives.hax.Tuple0.mk
      (fun _ d =>
        (do
        (main.call_everything (Enum.D d)) : RustM rust_primitives.hax.Tuple0))))
    rust_primitives.hax.Tuple0.mk))

end new_tests.rustc_coverage__branch__match_arms

