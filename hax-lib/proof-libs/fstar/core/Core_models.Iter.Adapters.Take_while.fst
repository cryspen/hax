module Core_models.Iter.Adapters.Take_while
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Rust_primitives

include Core_models.Bundle {t_TakeWhile as t_TakeWhile}

include Core_models.Bundle {impl__new__from__take_while as impl__new}

include Core_models.Bundle {impl_1__from__take_while as impl_1}
