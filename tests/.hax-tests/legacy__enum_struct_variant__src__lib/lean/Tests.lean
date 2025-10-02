
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

structure Tests.Legacy__enum_struct_variant__src__lib.Money where
  value : u64

instance Tests.Legacy__enum_struct_variant__src__lib.Impl :
  Core.Fmt.Debug Tests.Legacy__enum_struct_variant__src__lib.Money
  where


inductive Tests.Legacy__enum_struct_variant__src__lib.EnumWithStructVariant
: Type
| Funds (balance : Tests.Legacy__enum_struct_variant__src__lib.Money)
    : Tests.Legacy__enum_struct_variant__src__lib.EnumWithStructVariant 


instance Tests.Legacy__enum_struct_variant__src__lib.Impl_1 :
  Core.Fmt.Debug
  Tests.Legacy__enum_struct_variant__src__lib.EnumWithStructVariant
  where
  