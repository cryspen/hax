module Core_models.Result
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Bundle {t_Result as t_Result}

include Core_models.Bundle {Result_Ok as Result_Ok}

include Core_models.Bundle {Result_Err as Result_Err}

include Core_models.Bundle {impl__unwrap__from__result as impl__unwrap}

include Core_models.Bundle {impl__expect__from__result as impl__expect}

include Core_models.Bundle {impl__map__from__result as impl__map}

include Core_models.Bundle {impl__map_or__from__result as impl__map_or}

include Core_models.Bundle {impl__map_or_else__from__result as impl__map_or_else}

include Core_models.Bundle {impl__map_err as impl__map_err}

include Core_models.Bundle {impl__is_ok as impl__is_ok}

include Core_models.Bundle {impl__and_then__from__result as impl__and_then}

include Core_models.Bundle {impl__ok as impl__ok}
