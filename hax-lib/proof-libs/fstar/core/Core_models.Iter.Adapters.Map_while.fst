module Core_models.Iter.Adapters.Map_while
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Rust_primitives

include Core_models.Bundle {t_MapWhile as t_MapWhile}

include Core_models.Bundle {impl__new__from__map_while as impl__new}

include Core_models.Bundle {impl_1__from__map_while as impl_1}
