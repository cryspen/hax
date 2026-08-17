module Core_models.Iter.Sources.Once
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Bundle {t_Once as t_Once}

include Core_models.Bundle {Once as Once}

include Core_models.Bundle {once as once}

include Core_models.Bundle {impl__from__once as impl}

include Core_models.Bundle {impl_2__from__once as impl_2}

include Core_models.Bundle {impl_1__from__once as impl_1}
