
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


namespace new_tests.rustc_coverage__closure_bug

def main (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let truthy : Bool ←
    (rust_primitives.hax.machine_int.eq
      (← (core_models.iter.traits.exact_size.ExactSizeIterator.len
        std.env.Args (← (std.env.args rust_primitives.hax.Tuple0.mk))))
      (1 : usize));
  let a : (rust_primitives.hax.Tuple0 -> RustM Bool) :=
    (fun _ => (do if truthy then (pure true) else (pure false) : RustM Bool));
  let _ ←
    (core_models.ops.function.Fn.call
      (rust_primitives.hax.Tuple0 -> RustM Bool)
      rust_primitives.hax.Tuple0 a rust_primitives.hax.Tuple0.mk);
  let _ ←
    if truthy then
      let _ ←
        (core_models.ops.function.Fn.call
          (rust_primitives.hax.Tuple0 -> RustM Bool)
          rust_primitives.hax.Tuple0 a rust_primitives.hax.Tuple0.mk);
      (pure rust_primitives.hax.Tuple0.mk)
    else
      (pure rust_primitives.hax.Tuple0.mk);
  let b : (rust_primitives.hax.Tuple0 -> RustM Bool) :=
    (fun _ => (do if truthy then (pure true) else (pure false) : RustM Bool));
  let _ ←
    (core_models.ops.function.Fn.call
      (rust_primitives.hax.Tuple0 -> RustM Bool)
      rust_primitives.hax.Tuple0 b rust_primitives.hax.Tuple0.mk);
  let _ ←
    if truthy then
      let _ ←
        (core_models.ops.function.Fn.call
          (rust_primitives.hax.Tuple0 -> RustM Bool)
          rust_primitives.hax.Tuple0 b rust_primitives.hax.Tuple0.mk);
      (pure rust_primitives.hax.Tuple0.mk)
    else
      (pure rust_primitives.hax.Tuple0.mk);
  let c : (rust_primitives.hax.Tuple0 -> RustM Bool) :=
    (fun _ => (do if truthy then (pure true) else (pure false) : RustM Bool));
  let _ ←
    (core_models.ops.function.Fn.call
      (rust_primitives.hax.Tuple0 -> RustM Bool)
      rust_primitives.hax.Tuple0 c rust_primitives.hax.Tuple0.mk);
  let _ ←
    if truthy then
      let _ ←
        (core_models.ops.function.Fn.call
          (rust_primitives.hax.Tuple0 -> RustM Bool)
          rust_primitives.hax.Tuple0 c rust_primitives.hax.Tuple0.mk);
      (pure rust_primitives.hax.Tuple0.mk)
    else
      (pure rust_primitives.hax.Tuple0.mk);
  let d : (rust_primitives.hax.Tuple0 -> RustM Bool) :=
    (fun _ => (do if truthy then (pure true) else (pure false) : RustM Bool));
  let _ ←
    (core_models.ops.function.Fn.call
      (rust_primitives.hax.Tuple0 -> RustM Bool)
      rust_primitives.hax.Tuple0 d rust_primitives.hax.Tuple0.mk);
  if truthy then
    let _ ←
      (core_models.ops.function.Fn.call
        (rust_primitives.hax.Tuple0 -> RustM Bool)
        rust_primitives.hax.Tuple0 d rust_primitives.hax.Tuple0.mk);
    (pure rust_primitives.hax.Tuple0.mk)
  else
    (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__closure_bug

