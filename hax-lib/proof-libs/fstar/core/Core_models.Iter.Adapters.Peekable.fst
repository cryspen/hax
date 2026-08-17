module Core_models.Iter.Adapters.Peekable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Bundle {t_Peekable as t_Peekable}

include Core_models.Bundle {impl__new__from__peekable as impl__new}

include Core_models.Bundle {impl__peek as impl__peek}

include Core_models.Bundle {impl__next_if as impl__next_if}

include Core_models.Bundle {impl__next_if_eq as impl__next_if_eq}

include Core_models.Bundle {impl__next_if_map as impl__next_if_map}

include Core_models.Bundle {impl_1__from__peekable as impl_1}
