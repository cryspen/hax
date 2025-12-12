module Core_models.Iter.Traits.Iterator
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Iter.Bundle {t_Iterator as t_Iterator}

include Core_models.Iter.Bundle {f_Item as f_Item}

include Core_models.Iter.Bundle {f_next_pre as f_next_pre}

include Core_models.Iter.Bundle {f_next_post as f_next_post}

include Core_models.Iter.Bundle {f_next as f_next}

include Core_models.Iter.Bundle {fold as fold}

include Core_models.Iter.Bundle {enumerate as enumerate}

include Core_models.Iter.Bundle {step_by as step_by}

include Core_models.Iter.Bundle {map as map}

include Core_models.Iter.Bundle {all as all}

include Core_models.Iter.Bundle {take as take}

include Core_models.Iter.Bundle {flat_map as flat_map}

include Core_models.Iter.Bundle {flatten as flatten}

include Core_models.Iter.Bundle {zip as zip}
