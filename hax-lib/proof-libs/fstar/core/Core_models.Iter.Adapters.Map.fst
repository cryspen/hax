module Core_models.Iter.Adapters.Map
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Bundle {t_Map as t_Map}

include Core_models.Bundle {impl__new__from__map as impl__new}

include Core_models.Bundle {impl_1__from__map as impl_1}

include Core_models.Bundle {impl_2__from__map as impl_2}

include Core_models.Bundle {impl_3__from__map as impl_3}
