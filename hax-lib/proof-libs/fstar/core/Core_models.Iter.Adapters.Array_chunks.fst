module Core_models.Iter.Adapters.Array_chunks
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Bundle {t_ArrayChunks as t_ArrayChunks}

include Core_models.Bundle {impl__new__from__array_chunks as impl__new}

include Core_models.Bundle {impl_1__into_remainder as impl_1__into_remainder}

include Core_models.Bundle {impl_2__from__array_chunks as impl_2}
