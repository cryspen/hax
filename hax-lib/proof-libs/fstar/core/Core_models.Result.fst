module Core_models.Result
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Bundle {t_Result as t_Result}

include Core_models.Bundle {Result_Ok as Result_Ok}

include Core_models.Bundle {Result_Err as Result_Err}

include Core_models.Bundle {impl_1__is_ok as impl_1__is_ok}

include Core_models.Bundle {impl_1__is_ok_and as impl_1__is_ok_and}

include Core_models.Bundle {impl_1__is_err as impl_1__is_err}

include Core_models.Bundle {impl_1__is_err_and as impl_1__is_err_and}

include Core_models.Bundle {impl_1__as_ref as impl_1__as_ref}

include Core_models.Bundle {impl_1__expect as impl_1__expect}

include Core_models.Bundle {impl_1__unwrap as impl_1__unwrap}

include Core_models.Bundle {impl_1__expect_err as impl_1__expect_err}

include Core_models.Bundle {impl_1__unwrap_err as impl_1__unwrap_err}

include Core_models.Bundle {impl_1__unwrap_or_else as impl_1__unwrap_or_else}

include Core_models.Bundle {impl_1__unwrap_or_default as impl_1__unwrap_or_default}

include Core_models.Bundle {impl_1__map as impl_1__map}

include Core_models.Bundle {impl_1__map_or as impl_1__map_or}

include Core_models.Bundle {impl_1__map_or_else as impl_1__map_or_else}

include Core_models.Bundle {impl_1__map_or_default as impl_1__map_or_default}

include Core_models.Bundle {impl_1__inspect as impl_1__inspect}

include Core_models.Bundle {impl_1__inspect_err as impl_1__inspect_err}

include Core_models.Bundle {impl_1__ok as impl_1__ok}

include Core_models.Bundle {impl_1__err as impl_1__err}

include Core_models.Bundle {impl_1__and as impl_1__and}

include Core_models.Bundle {impl_1__and_then as impl_1__and_then}

include Core_models.Bundle {impl_1__or as impl_1__or}

include Core_models.Bundle {impl_1__or_else as impl_1__or_else}

include Core_models.Bundle {impl_1__unwrap_or as impl_1__unwrap_or}

include Core_models.Bundle {impl_1__map_err as impl_1__map_err}

include Core_models.Bundle {impl_1__unwrap_unchecked as impl_1__unwrap_unchecked}

include Core_models.Bundle {impl_1__unwrap_err_unchecked as impl_1__unwrap_err_unchecked}

include Core_models.Bundle {impl_1__iter as impl_1__iter}

include Core_models.Bundle {impl_2__cloned as impl_2__cloned}

include Core_models.Bundle {impl_3__transpose as impl_3__transpose}

include Core_models.Bundle {impl_4__flatten as impl_4__flatten}

include Core_models.Bundle {impl_5__from__result as impl_5}

include Core_models.Bundle {impl_6__from__result as impl_6}

include Core_models.Bundle {impl__from__result as impl}

include Core_models.Bundle {impl_7__from__result as impl_7}

include Core_models.Bundle {t_Iter__from__result as t_Iter}

include Core_models.Bundle {Iter__from__result as Iter}

include Core_models.Bundle {impl_8__from__result as impl_8}

include Core_models.Bundle {t_IntoIter__from__result as t_IntoIter}

include Core_models.Bundle {IntoIter__from__result as IntoIter}

include Core_models.Bundle {impl_10__from__result as impl_10}

include Core_models.Bundle {impl_11__from__result as impl_11}

include Core_models.Bundle {impl_12__as_deref as impl_12__as_deref}

include Core_models.Bundle {impl_14__copied as impl_14__copied}

include Core_models.Bundle {impl_15__into_ok as impl_15__into_ok}

include Core_models.Bundle {impl_16__into_err as impl_16__into_err}
