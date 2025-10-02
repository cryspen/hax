
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

def Tests.Rustc_tests__inline_dead.dead
  (_ : Rust_primitives.Hax.Tuple0)
  : Result u32
  := do
  (42 : u32)

def Tests.Rustc_tests__inline_dead.live
  -- Unsupported const param (_ : Rust_primitives.Hax.Tuple0)
  : Result u32
  := do
  (← if B then do
    (← Tests.Rustc_tests__inline_dead.dead Rust_primitives.Hax.Tuple0.mk)
  else do
    (0 : u32))

def Tests.Rustc_tests__inline_dead.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let args : (RustArray Core.Fmt.Rt.Argument (1 : usize)) ← (pure
    #v[(← Core.Fmt.Rt.Impl.new_display u32
             (← Tests.Rustc_tests__inline_dead.live false
                 Rust_primitives.Hax.Tuple0.mk))]);
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_v1 (2 : usize) (1 : usize)
            #v["", "
"]
            args)));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  let f : Bool -> Result Rust_primitives.Hax.Tuple0 ← (pure
    (fun x => (do
        let _ ← (pure
          (← if true then do
            let _ ← (pure (← Hax_lib.assert x));
            Rust_primitives.Hax.Tuple0.mk
          else do
            Rust_primitives.Hax.Tuple0.mk));
        Rust_primitives.Hax.Tuple0.mk : Result Rust_primitives.Hax.Tuple0)));
  let _ ← (pure
    (← Core.Ops.Function.Fn.call f (Rust_primitives.Hax.Tuple1.mk false)));
  Rust_primitives.Hax.Tuple0.mk