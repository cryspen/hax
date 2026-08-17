module Core_models.Iter.Adapters.Map_windows
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Bundle {t_MapWindows as t_MapWindows}

include Core_models.Bundle {impl__new__from__map_windows as impl__new}

include Core_models.Bundle {impl_1__from__map_windows as impl_1}
