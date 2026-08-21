module Core_models.Iter.Adapters.Intersperse
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Bundle {t_Intersperse as t_Intersperse}

include Core_models.Bundle {impl__new__from__intersperse as impl__new}

include Core_models.Bundle {impl_1__from__intersperse as impl_1}

include Core_models.Bundle {t_IntersperseWith as t_IntersperseWith}

include Core_models.Bundle {impl_2__new as impl_2__new}

include Core_models.Bundle {impl_3__from__intersperse as impl_3}
