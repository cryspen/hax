module Core_models.Ops.Control_flow
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Bundle {t_ControlFlow as t_ControlFlow}

include Core_models.Bundle {ControlFlow_Continue as ControlFlow_Continue}

include Core_models.Bundle {ControlFlow_Break as ControlFlow_Break}

include Core_models.Bundle {impl__is_break as impl__is_break}

include Core_models.Bundle {impl__is_continue as impl__is_continue}

include Core_models.Bundle {impl__break_value as impl__break_value}

include Core_models.Bundle {impl__break_ok as impl__break_ok}

include Core_models.Bundle {impl__map_break as impl__map_break}

include Core_models.Bundle {impl__continue_value as impl__continue_value}

include Core_models.Bundle {impl__continue_ok as impl__continue_ok}

include Core_models.Bundle {impl__map_continue as impl__map_continue}

include Core_models.Bundle {impl_1__into_value as impl_1__into_value}
