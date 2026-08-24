module Core_models.Iter.Traits.Collect
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Bundle {t_IntoIterator as t_IntoIterator}

include Core_models.Bundle {f_Item as f_Item}

include Core_models.Bundle {f_IntoIter as f_IntoIter}

include Core_models.Bundle {f_into_iter_pre as f_into_iter_pre}

include Core_models.Bundle {f_into_iter_post as f_into_iter_post}

include Core_models.Bundle {f_into_iter as f_into_iter}

include Core_models.Bundle {t_FromIterator as t_FromIterator}

include Core_models.Bundle {f_from_iter_pre as f_from_iter_pre}

include Core_models.Bundle {f_from_iter_post as f_from_iter_post}

include Core_models.Bundle {f_from_iter as f_from_iter}
