module Core_models.Result
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Bundle {t_Result as t_Result}

include Core_models.Bundle {Result_Ok as Result_Ok}

include Core_models.Bundle {Result_Err as Result_Err}

include Core_models.Bundle {impl_3__is_ok as impl_3__is_ok}

include Core_models.Bundle {impl_3__is_ok_and as impl_3__is_ok_and}

include Core_models.Bundle {impl_3__is_err as impl_3__is_err}

include Core_models.Bundle {impl_3__is_err_and as impl_3__is_err_and}

include Core_models.Bundle {impl_3__as_ref as impl_3__as_ref}

include Core_models.Bundle {impl_3__expect as impl_3__expect}

include Core_models.Bundle {impl_3__unwrap as impl_3__unwrap}

include Core_models.Bundle {impl_3__expect_err as impl_3__expect_err}

include Core_models.Bundle {impl_3__unwrap_err as impl_3__unwrap_err}

include Core_models.Bundle {impl_3__unwrap_or as impl_3__unwrap_or}

include Core_models.Bundle {impl_3__unwrap_or_else as impl_3__unwrap_or_else}

include Core_models.Bundle {impl_3__unwrap_or_default as impl_3__unwrap_or_default}

include Core_models.Bundle {impl_3__map as impl_3__map}

include Core_models.Bundle {impl_3__map_or as impl_3__map_or}

include Core_models.Bundle {impl_3__map_or_else as impl_3__map_or_else}

include Core_models.Bundle {impl_3__map_or_default as impl_3__map_or_default}

include Core_models.Bundle {impl_3__map_err as impl_3__map_err}

include Core_models.Bundle {impl_3__inspect as impl_3__inspect}

include Core_models.Bundle {impl_3__inspect_err as impl_3__inspect_err}

include Core_models.Bundle {impl_3__ok as impl_3__ok}

include Core_models.Bundle {impl_3__err as impl_3__err}

include Core_models.Bundle {impl_3__and as impl_3__and}

include Core_models.Bundle {impl_3__and_then as impl_3__and_then}

include Core_models.Bundle {impl_3__or as impl_3__or}

include Core_models.Bundle {impl_3__or_else as impl_3__or_else}

include Core_models.Bundle {impl__cloned as impl__cloned}

include Core_models.Bundle {impl_1__transpose as impl_1__transpose}

include Core_models.Bundle {impl_2__flatten as impl_2__flatten}
