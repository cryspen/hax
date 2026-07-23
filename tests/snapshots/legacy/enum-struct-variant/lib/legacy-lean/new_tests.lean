
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


namespace new_tests.legacy__enum_struct_variant__lib

structure Money where
  value : u64

@[instance] opaque Impl.AssociatedTypes :
  core_models.fmt.Debug.AssociatedTypes Money :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl :
  core_models.fmt.Debug Money :=
  by constructor <;> exact Inhabited.default

inductive EnumWithStructVariant : Type
| Funds (balance : Money) : EnumWithStructVariant

@[instance] opaque Impl_1.AssociatedTypes :
  core_models.fmt.Debug.AssociatedTypes EnumWithStructVariant :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1 :
  core_models.fmt.Debug EnumWithStructVariant :=
  by constructor <;> exact Inhabited.default

end new_tests.legacy__enum_struct_variant__lib

