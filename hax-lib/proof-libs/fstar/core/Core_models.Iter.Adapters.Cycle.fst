module Core_models.Iter.Adapters.Cycle
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Bundle {t_Cycle as t_Cycle}

include Core_models.Bundle {impl__new__from__cycle as impl__new}

include Core_models.Bundle {impl_1__from__cycle as impl_1}
