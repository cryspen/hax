module Core_models.Iter.Adapters.Skip
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Iter.Bundle {t_Skip as t_Skip}

include Core_models.Iter.Bundle {impl__new__from__skip as impl__new}

include Core_models.Iter.Bundle {impl_1__from__skip as impl_1}
