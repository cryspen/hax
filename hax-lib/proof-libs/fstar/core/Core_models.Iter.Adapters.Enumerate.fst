module Core_models.Iter.Adapters.Enumerate
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Bundle {t_Enumerate as t_Enumerate}

include Core_models.Bundle {impl__new as impl__new}

include Core_models.Bundle {impl_1__from__enumerate as impl_1}
