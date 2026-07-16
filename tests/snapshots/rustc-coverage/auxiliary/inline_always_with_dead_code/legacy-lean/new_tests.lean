
-- Legacy lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/legacy-lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace new_tests.rustc_coverage__auxiliary__inline_always_with_dead_code.foo

@[spec]
def called (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def uncalled (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__auxiliary__inline_always_with_dead_code.foo


namespace new_tests.rustc_coverage__auxiliary__inline_always_with_dead_code.bar

@[spec]
def call_me (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ←
    (new_tests.rustc_coverage__auxiliary__inline_always_with_dead_code.foo.called
      rust_primitives.hax.Tuple0.mk);
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__auxiliary__inline_always_with_dead_code.bar


namespace new_tests.rustc_coverage__auxiliary__inline_always_with_dead_code.baz

@[spec]
def call_me (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ←
    (new_tests.rustc_coverage__auxiliary__inline_always_with_dead_code.foo.called
      rust_primitives.hax.Tuple0.mk);
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__auxiliary__inline_always_with_dead_code.baz
