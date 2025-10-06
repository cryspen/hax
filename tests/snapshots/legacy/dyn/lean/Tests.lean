
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
  stringify : Self -> Result S

instance Tests.Legacy__dyn.Impl :
  Tests.Legacy__dyn.Printable i32 Alloc.String.String
  where
  stringify (self : i32) := do (← Alloc.String.ToString.to_string self)

def Tests.Legacy__dyn.print
  (a : (Alloc.Boxed.Box sorry 
-- unsupported type
 Alloc.Alloc.Global))
  : Result Rust_primitives.Hax.Tuple0
  := do
  let args : (RustArray Core.Fmt.Rt.Argument (1 : usize)) ← (pure
    #v[(← Core.Fmt.Rt.Impl.new_display Alloc.String.String
             (← Tests.Legacy__dyn.Printable.stringify a))]);
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_v1 (2 : usize) (1 : usize)
            #v["", "
"]
            args)));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  Rust_primitives.Hax.Tuple0.mk