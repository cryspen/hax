module Core_models.Iter.Traits.Exact_size
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Bundle {t_ExactSizeIterator as t_ExactSizeIterator}

include Core_models.Bundle {f_len_pre as f_len_pre}

include Core_models.Bundle {f_len_post as f_len_post}

include Core_models.Bundle {f_len as f_len}

include Core_models.Bundle {t_ExactSizeIteratorMethods as t_ExactSizeIteratorMethods}

include Core_models.Bundle {f_is_empty_pre as f_is_empty_pre}

include Core_models.Bundle {f_is_empty_post as f_is_empty_post}

include Core_models.Bundle {f_is_empty as f_is_empty}

include Core_models.Bundle {impl__from__exact_size as impl}
