
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


namespace new_tests.rustc_coverage__branch__guard

--  @fail(extraction): proverif(HAX0008, HAX0008)
def branch_match_guard (x : (core_models.option.Option u32)) :
    RustM rust_primitives.hax.Tuple0 := do
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
  match x with
    | (core_models.option.Option.Some  0) =>
      let _ ←
        (std.io.stdio._print
          (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize)) #v["zero
"])));
      let _ := rust_primitives.hax.Tuple0.mk;
      (pure rust_primitives.hax.Tuple0.mk)
    | _ =>
      match
        (← match x with
          | (core_models.option.Option.Some  x) =>
            match
              (← (rust_primitives.hax.machine_int.eq
                (← (x %? (2 : u32)))
                (0 : u32)))
            with
              | true =>
                let _ ←
                  (std.io.stdio._print
                    (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize))
                      #v["is nonzero and even
"])));
                let _ := rust_primitives.hax.Tuple0.mk;
                (pure (core_models.option.Option.Some
                  rust_primitives.hax.Tuple0.mk))
              | _ => (pure core_models.option.Option.None)
          | _ => (pure core_models.option.Option.None))
      with
        | (core_models.option.Option.Some  x) => (pure x)
        | (core_models.option.Option.None ) =>
          match
            (← match x with
              | (core_models.option.Option.Some  x) =>
                match
                  (← (rust_primitives.hax.machine_int.eq
                    (← (x %? (3 : u32)))
                    (0 : u32)))
                with
                  | true =>
                    let _ ←
                      (std.io.stdio._print
                        (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize))
                          #v["is nonzero and odd, but divisible by 3
"])));
                    let _ := rust_primitives.hax.Tuple0.mk;
                    (pure (core_models.option.Option.Some
                      rust_primitives.hax.Tuple0.mk))
                  | _ => (pure core_models.option.Option.None)
              | _ => (pure core_models.option.Option.None))
          with
            | (core_models.option.Option.Some  x) => (pure x)
            | (core_models.option.Option.None ) =>
              let _ ←
                (std.io.stdio._print
                  (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize))
                    #v["something else
"])));
              let _ := rust_primitives.hax.Tuple0.mk;
              (pure rust_primitives.hax.Tuple0.mk)

def main (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ← (branch_match_guard (core_models.option.Option.Some (0 : u32)));
  let _ ← (branch_match_guard (core_models.option.Option.Some (2 : u32)));
  let _ ← (branch_match_guard (core_models.option.Option.Some (6 : u32)));
  let _ ← (branch_match_guard (core_models.option.Option.Some (3 : u32)));
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__branch__guard

