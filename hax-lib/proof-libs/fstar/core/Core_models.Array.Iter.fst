module Core_models.Array.Iter
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Bundle {t_IntoIter as t_IntoIter}

include Core_models.Bundle {IntoIter as IntoIter}

include Core_models.Bundle {impl as impl}
