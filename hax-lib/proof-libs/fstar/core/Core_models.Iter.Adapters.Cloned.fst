module Core_models.Iter.Adapters.Cloned
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Bundle {t_Cloned as t_Cloned}

include Core_models.Bundle {impl__new as impl__new}

include Core_models.Bundle {impl_1__from__cloned as impl_1}

include Core_models.Bundle {impl_2__from__cloned as impl_2}

include Core_models.Bundle {impl_3__from__cloned as impl_3}
