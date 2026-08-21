module Core_models.Iter.Adapters.Copied
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Bundle {t_Copied as t_Copied}

include Core_models.Bundle {impl__new__from__copied as impl__new}

include Core_models.Bundle {impl_1__from__copied as impl_1}

include Core_models.Bundle {impl_2__from__copied as impl_2}

include Core_models.Bundle {impl_3__from__copied as impl_3}
