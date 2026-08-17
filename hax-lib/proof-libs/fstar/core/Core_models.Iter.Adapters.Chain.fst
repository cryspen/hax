module Core_models.Iter.Adapters.Chain
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Bundle {t_Chain as t_Chain}

include Core_models.Bundle {impl__new__from__chain as impl__new}

include Core_models.Bundle {chain as chain}

include Core_models.Bundle {impl_1 as impl_1}

include Core_models.Bundle {impl_2__from__chain as impl_2}
