module Core_models.Iter.Adapters.Skip_while
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Bundle {t_SkipWhile as t_SkipWhile}

include Core_models.Bundle {impl__new__from__skip_while as impl__new}

include Core_models.Bundle {impl_1__from__skip_while as impl_1}
