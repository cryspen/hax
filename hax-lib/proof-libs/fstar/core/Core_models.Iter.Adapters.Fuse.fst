module Core_models.Iter.Adapters.Fuse
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Bundle {t_Fuse as t_Fuse}

include Core_models.Bundle {impl_1__new as impl_1__new}

include Core_models.Bundle {impl_2__from__fuse as impl_2}

include Core_models.Bundle {impl_3__from__fuse as impl_3}

include Core_models.Bundle {impl__from__fuse as impl}
