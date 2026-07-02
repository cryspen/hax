
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/legacy-lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace new_tests.legacy__proverif_basic_structs__lib

structure Ainitial where
  x : u8

structure A where
  one : usize
  two : usize

structure B where
  _0 : usize

end new_tests.legacy__proverif_basic_structs__lib

