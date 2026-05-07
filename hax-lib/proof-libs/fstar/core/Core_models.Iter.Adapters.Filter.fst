module Core_models.Iter.Adapters.Filter
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Iter.Bundle {t_Filter as t_Filter}

include Core_models.Iter.Bundle {impl__new__from__filter as impl__new}

include Core_models.Iter.Bundle {impl_1__from__filter as impl_1}
