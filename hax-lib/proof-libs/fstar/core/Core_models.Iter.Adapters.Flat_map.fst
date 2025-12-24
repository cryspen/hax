module Core_models.Iter.Adapters.Flat_map
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Iter.Bundle {t_FlatMap as t_FlatMap}

include Core_models.Iter.Bundle {impl__new__from__flat_map as impl__new}

include Core_models.Iter.Bundle {impl_1__from__flat_map as impl_1}
