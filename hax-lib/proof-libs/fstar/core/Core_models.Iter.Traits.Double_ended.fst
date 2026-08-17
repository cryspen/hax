module Core_models.Iter.Traits.Double_ended
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Bundle {t_DoubleEndedIterator as t_DoubleEndedIterator}

include Core_models.Bundle {f_next_back_pre as f_next_back_pre}

include Core_models.Bundle {f_next_back_post as f_next_back_post}

include Core_models.Bundle {f_next_back as f_next_back}

include Core_models.Bundle {t_DoubleEndedIteratorMethods as t_DoubleEndedIteratorMethods}

include Core_models.Bundle {f_advance_back_by_pre as f_advance_back_by_pre}

include Core_models.Bundle {f_advance_back_by_post as f_advance_back_by_post}

include Core_models.Bundle {f_advance_back_by as f_advance_back_by}

include Core_models.Bundle {f_nth_back_pre as f_nth_back_pre}

include Core_models.Bundle {f_nth_back_post as f_nth_back_post}

include Core_models.Bundle {f_nth_back as f_nth_back}

include Core_models.Bundle {f_rfind_pre as f_rfind_pre}

include Core_models.Bundle {f_rfind_post as f_rfind_post}

include Core_models.Bundle {f_rfind as f_rfind}

include Core_models.Bundle {f_rfold_pre as f_rfold_pre}

include Core_models.Bundle {f_rfold_post as f_rfold_post}

include Core_models.Bundle {f_rfold as f_rfold}

include Core_models.Bundle {f_try_rfold_pre as f_try_rfold_pre}

include Core_models.Bundle {f_try_rfold_post as f_try_rfold_post}

include Core_models.Bundle {f_try_rfold as f_try_rfold}

include Core_models.Bundle {iter_advance_back_by as iter_advance_back_by}

include Core_models.Bundle {iter_nth_back as iter_nth_back}

include Core_models.Bundle {iter_rfind as iter_rfind}

include Core_models.Bundle {iter_rfold as iter_rfold}

include Core_models.Bundle {iter_try_rfold as iter_try_rfold}

include Core_models.Bundle {impl__from__double_ended as impl}
