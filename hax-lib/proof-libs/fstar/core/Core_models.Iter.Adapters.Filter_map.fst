module Core_models.Iter.Adapters.Filter_map
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Bundle {t_FilterMap as t_FilterMap}

include Core_models.Bundle {impl__new__from__filter_map as impl__new}

include Core_models.Bundle {impl_1__from__filter_map as impl_1}
