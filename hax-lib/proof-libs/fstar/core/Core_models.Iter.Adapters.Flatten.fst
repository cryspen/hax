module Core_models.Iter.Adapters.Flatten
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Iter.Bundle {t_Flatten as t_Flatten}

include Core_models.Iter.Bundle {impl__new__from__flatten as impl__new}

include Core_models.Iter.Bundle {impl_1__from__flatten as impl_1}
