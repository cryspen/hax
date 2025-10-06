
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

structure Tests.Legacy__proverif_basic_structs.Ainitial where
  x : u8

structure Tests.Legacy__proverif_basic_structs.A where
  one : usize
  two : usize

structure Tests.Legacy__proverif_basic_structs.B where
  _0 : usize