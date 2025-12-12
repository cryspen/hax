module Core_models.Iter.Adapters.Step_by
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Iter.Bundle {t_StepBy as t_StepBy}

include Core_models.Iter.Bundle {impl__new__from__step_by as impl__new}

include Core_models.Iter.Bundle {impl_1__from__step_by as impl_1}
