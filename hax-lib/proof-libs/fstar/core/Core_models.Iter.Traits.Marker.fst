module Core_models.Iter.Traits.Marker
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Bundle {t_FusedIterator as t_FusedIterator}

include Core_models.Bundle {t_TrustedLen as t_TrustedLen}
