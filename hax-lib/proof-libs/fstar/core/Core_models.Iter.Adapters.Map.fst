module Core_models.Iter.Adapters.Map
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Iter.Bundle {t_Map as t_Map}

include Core_models.Iter.Bundle {impl__new__from__map as impl__new}

include Core_models.Iter.Bundle {impl_1__from__map as impl_1}
