module Core_models.Iter.Adapters.Rev
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Bundle {t_Rev as t_Rev}

include Core_models.Bundle {impl__new__from__rev as impl__new}

include Core_models.Bundle {impl__into_inner as impl__into_inner}

include Core_models.Bundle {impl_1__from__rev as impl_1}

include Core_models.Bundle {impl_2__from__rev as impl_2}

include Core_models.Bundle {impl_3__from__rev as impl_3}
