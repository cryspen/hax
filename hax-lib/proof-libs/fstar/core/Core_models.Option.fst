module Core_models.Option
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Bundle {t_Option as t_Option}

include Core_models.Bundle {Option_Some as Option_Some}

include Core_models.Bundle {Option_None as Option_None}

include Core_models.Bundle {impl__is_some as impl__is_some}

include Core_models.Bundle {impl__is_some_and as impl__is_some_and}

include Core_models.Bundle {impl__is_none as impl__is_none}

include Core_models.Bundle {impl__is_none_or as impl__is_none_or}

include Core_models.Bundle {impl__as_ref__from__option as impl__as_ref}

include Core_models.Bundle {impl__expect as impl__expect}

include Core_models.Bundle {impl__unwrap as impl__unwrap}

include Core_models.Bundle {impl__unwrap_or as impl__unwrap_or}

include Core_models.Bundle {impl__unwrap_or_else as impl__unwrap_or_else}

include Core_models.Bundle {impl__unwrap_or_default as impl__unwrap_or_default}

include Core_models.Bundle {impl__map__from__option as impl__map}

include Core_models.Bundle {impl__map_or as impl__map_or}

include Core_models.Bundle {impl__map_or_else as impl__map_or_else}

include Core_models.Bundle {impl__map_or_default as impl__map_or_default}

include Core_models.Bundle {impl__ok_or as impl__ok_or}

include Core_models.Bundle {impl__ok_or_else as impl__ok_or_else}

include Core_models.Bundle {impl__and_then as impl__and_then}

include Core_models.Bundle {impl__take as impl__take}

include Core_models.Bundle {impl__filter as impl__filter}

include Core_models.Bundle {impl__or as impl__or}

include Core_models.Bundle {impl__or_else as impl__or_else}

include Core_models.Bundle {impl__xor as impl__xor}

include Core_models.Bundle {impl__zip as impl__zip}

include Core_models.Bundle {impl__inspect as impl__inspect}

include Core_models.Bundle {impl__and as impl__and}

include Core_models.Bundle {impl__as_slice as impl__as_slice}

include Core_models.Bundle {impl__unwrap_unchecked as impl__unwrap_unchecked}

include Core_models.Bundle {impl__iter as impl__iter}

include Core_models.Bundle {impl__into_flat_iter as impl__into_flat_iter}

include Core_models.Bundle {impl__insert as impl__insert}

include Core_models.Bundle {impl__get_or_insert as impl__get_or_insert}

include Core_models.Bundle {impl__get_or_insert_with as impl__get_or_insert_with}

include Core_models.Bundle {impl__get_or_insert_default as impl__get_or_insert_default}

include Core_models.Bundle {impl__get_or_try_insert_with as impl__get_or_try_insert_with}

include Core_models.Bundle {impl__replace as impl__replace}

include Core_models.Bundle {impl__zip_with as impl__zip_with}

include Core_models.Bundle {impl__reduce as impl__reduce}

include Core_models.Bundle {impl_1__flatten as impl_1__flatten}

include Core_models.Bundle {impl_2__from__option as impl_2}

include Core_models.Bundle {impl_3__from__option as impl_3}

include Core_models.Bundle {impl_4__from__option as impl_4}

include Core_models.Bundle {impl_5__transpose as impl_5__transpose}

include Core_models.Bundle {impl_6__from__option as impl_6}

include Core_models.Bundle {impl_7__unzip as impl_7__unzip}

include Core_models.Bundle {impl_8__cloned as impl_8__cloned}

include Core_models.Bundle {impl_9__as_deref as impl_9__as_deref}

include Core_models.Bundle {impl_10__copied as impl_10__copied}

include Core_models.Bundle {impl_12__flatten_ref as impl_12__flatten_ref}

include Core_models.Bundle {t_Iter as t_Iter}

include Core_models.Bundle {Iter as Iter}

include Core_models.Bundle {impl_14__from__option as impl_14}

include Core_models.Bundle {t_IntoIter__from__option as t_IntoIter}

include Core_models.Bundle {IntoIter__from__option as IntoIter}

include Core_models.Bundle {impl_16__from__option as impl_16}

include Core_models.Bundle {impl_17__from__option as impl_17}

include Core_models.Bundle {t_OptionFlatten as t_OptionFlatten}

include Core_models.Bundle {OptionFlatten as OptionFlatten}

include Core_models.Bundle {impl_18__from__option as impl_18}
