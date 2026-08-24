module Core_models.Iter.Adapters.Inspect
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Bundle {t_Inspect as t_Inspect}

include Core_models.Bundle {impl__new__from__inspect as impl__new}

include Core_models.Bundle {impl_1__from__inspect as impl_1}
