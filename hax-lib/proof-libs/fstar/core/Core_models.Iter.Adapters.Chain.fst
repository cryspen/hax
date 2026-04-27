module Core_models.Iter.Adapters.Chain
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Iter.Bundle {t_Chain as t_Chain}

include Core_models.Iter.Bundle {impl__new as impl__new}

include Core_models.Iter.Bundle {impl_1 as impl_1}
