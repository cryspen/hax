
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

class Tests.Legacy__dyn.Printable (Self : Type) (S : Type) where
  stringify : (Self -> Result S)

instance Tests.Legacy__dyn.Impl :
  Tests.Legacy__dyn.Printable i32 Alloc.String.String
  where
  stringify (self : i32) := do (Alloc.String.ToString.to_string self)

--  @fail(extraction): coq(HAX0008), ssprove(HAX0008)
--  @fail(extraction): proverif(HAX0008)
def Tests.Legacy__dyn.print
  (a : (Alloc.Boxed.Box sorry Alloc.Alloc.Global))
  : Result Rust_primitives.Hax.Tuple0
  := do
  let args : (Rust_primitives.Hax.Tuple1 Alloc.String.String) :=
    (Rust_primitives.Hax.Tuple1.mk
      (← (Tests.Legacy__dyn.Printable.stringify a)));
  let args : (RustArray Core.Fmt.Rt.Argument 1) :=
    #v[(← (Core.Fmt.Rt.Impl.new_display Alloc.String.String
           (Rust_primitives.Hax.Tuple1._0 args)))];
  let _ ←
    (Std.Io.Stdio._print
      (← (Core.Fmt.Rt.Impl_1.new_v1 (2 : usize) (1 : usize) #v["", "
"] args)));
  let _ := Rust_primitives.Hax.Tuple0.mk;
  (pure Rust_primitives.Hax.Tuple0.mk)