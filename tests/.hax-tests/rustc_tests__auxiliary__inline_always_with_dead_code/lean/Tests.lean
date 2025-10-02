
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

def Tests.Rustc_tests__auxiliary__inline_always_with_dead_code.Foo.called
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__auxiliary__inline_always_with_dead_code.Foo.uncalled
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__auxiliary__inline_always_with_dead_code.Baz.call_me
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__auxiliary__inline_always_with_dead_code.Foo.called
        Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__auxiliary__inline_always_with_dead_code.Bar.call_me
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__auxiliary__inline_always_with_dead_code.Foo.called
        Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk