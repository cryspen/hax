module Core_models.Array.Iter
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Bundle {t_IntoIter as t_IntoIter}

include Core_models.Bundle {IntoIter as IntoIter}

include Core_models.Bundle {impl as impl}

include Core_models.Bundle {impl_1__new as impl_1__new}

include Core_models.Bundle {impl_1__empty as impl_1__empty}

include Core_models.Bundle {impl_1__as_slice as impl_1__as_slice}
