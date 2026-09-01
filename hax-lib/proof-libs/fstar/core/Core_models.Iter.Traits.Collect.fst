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

include Core_models.Bundle {t_Extend as t_Extend}

include Core_models.Bundle {f_extend_pre as f_extend_pre}

include Core_models.Bundle {f_extend_post as f_extend_post}

include Core_models.Bundle {f_extend as f_extend}

include Core_models.Bundle {t_ExtendMethods as t_ExtendMethods}

include Core_models.Bundle {f_extend_one_pre as f_extend_one_pre}

include Core_models.Bundle {f_extend_one_post as f_extend_one_post}

include Core_models.Bundle {f_extend_one as f_extend_one}

include Core_models.Bundle {f_extend_reserve_pre as f_extend_reserve_pre}

include Core_models.Bundle {f_extend_reserve_post as f_extend_reserve_post}

include Core_models.Bundle {f_extend_reserve as f_extend_reserve}

include Core_models.Bundle {impl__from__collect as impl}
