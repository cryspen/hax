module Core_models.Iter.Adapters.Fuse
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Rust_primitives

include Core_models.Bundle {t_Fuse as t_Fuse}

include Core_models.Bundle {impl__new__from__fuse as impl__new}

include Core_models.Bundle {impl_1__from__fuse as impl_1}
