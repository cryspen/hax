module Core_models.Iter.Adapters.Chain
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Bundle {t_Chain as t_Chain}

include Core_models.Bundle {impl__new__from__chain as impl__new}

include Core_models.Bundle {impl_1__from__chain as impl_1}
