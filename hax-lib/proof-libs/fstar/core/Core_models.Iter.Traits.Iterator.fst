module Core_models.Iter.Traits.Iterator
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Iter.Bundle {t_Iterator as t_Iterator}

include Core_models.Iter.Bundle {f_Item as f_Item}

include Core_models.Iter.Bundle {f_next_pre as f_next_pre}

include Core_models.Iter.Bundle {f_next_post as f_next_post}

include Core_models.Iter.Bundle {f_next as f_next}

include Core_models.Iter.Bundle {t_IteratorMethods as t_IteratorMethods}

include Core_models.Iter.Bundle {f_fold_pre as f_fold_pre}

include Core_models.Iter.Bundle {f_fold_post as f_fold_post}

include Core_models.Iter.Bundle {f_fold as f_fold}

include Core_models.Iter.Bundle {f_enumerate_pre as f_enumerate_pre}

include Core_models.Iter.Bundle {f_enumerate_post as f_enumerate_post}

include Core_models.Iter.Bundle {f_enumerate as f_enumerate}

include Core_models.Iter.Bundle {f_step_by_pre as f_step_by_pre}

include Core_models.Iter.Bundle {f_step_by_post as f_step_by_post}

include Core_models.Iter.Bundle {f_step_by as f_step_by}

include Core_models.Iter.Bundle {f_map_pre as f_map_pre}

include Core_models.Iter.Bundle {f_map_post as f_map_post}

include Core_models.Iter.Bundle {f_map as f_map}

include Core_models.Iter.Bundle {f_all_pre as f_all_pre}

include Core_models.Iter.Bundle {f_all_post as f_all_post}

include Core_models.Iter.Bundle {f_all as f_all}

include Core_models.Iter.Bundle {f_take_pre as f_take_pre}

include Core_models.Iter.Bundle {f_take_post as f_take_post}

include Core_models.Iter.Bundle {f_take as f_take}

include Core_models.Iter.Bundle {f_flat_map_pre as f_flat_map_pre}

include Core_models.Iter.Bundle {f_flat_map_post as f_flat_map_post}

include Core_models.Iter.Bundle {f_flat_map as f_flat_map}

include Core_models.Iter.Bundle {f_flatten_pre as f_flatten_pre}

include Core_models.Iter.Bundle {f_flatten_post as f_flatten_post}

include Core_models.Iter.Bundle {f_flatten as f_flatten}

include Core_models.Iter.Bundle {f_zip_pre as f_zip_pre}

include Core_models.Iter.Bundle {f_zip_post as f_zip_post}

include Core_models.Iter.Bundle {f_zip as f_zip}

include Core_models.Iter.Bundle {impl as impl}
