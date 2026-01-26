module Core_models.Iter.Adapters.Zip
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Iter.Bundle {t_Zip as t_Zip}

include Core_models.Iter.Bundle {impl__new__from__zip as impl__new}

include Core_models.Iter.Bundle {impl_1__from__zip as impl_1}
