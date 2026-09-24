module Core_models.Ops.Range
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Bundle {t_RangeTo as t_RangeTo}

include Core_models.Bundle {t_RangeFrom as t_RangeFrom}

include Core_models.Bundle {t_Range as t_Range}

include Core_models.Bundle {t_RangeFull as t_RangeFull}

include Core_models.Bundle {RangeFull as RangeFull}

include Core_models.Bundle {t_RangeInclusive as t_RangeInclusive}

include Core_models.Bundle {t_RangeToInclusive as t_RangeToInclusive}

include Core_models.Bundle {impl_11__from__range as impl_11}

include Core_models.Bundle {impl_12__from__range as impl_12}

include Core_models.Bundle {impl_13__from__range as impl_13}

include Core_models.Bundle {impl_14__from__range as impl_14}

include Core_models.Bundle {impl_15__from__range as impl_15}

include Core_models.Bundle {impl_16__from__range as impl_16}

include Core_models.Bundle {impl_17__from__range as impl_17}

include Core_models.Bundle {impl_18__from__range as impl_18}

include Core_models.Bundle {impl_19__from__range as impl_19}

include Core_models.Bundle {impl_20__from__range as impl_20}

include Core_models.Bundle {impl_21__from__range as impl_21}

include Core_models.Bundle {impl_22__from__range as impl_22}

include Core_models.Bundle {t_Bound as t_Bound}

include Core_models.Bundle {Bound_Included as Bound_Included}

include Core_models.Bundle {Bound_Excluded as Bound_Excluded}

include Core_models.Bundle {Bound_Unbounded as Bound_Unbounded}

include Core_models.Bundle {t_RangeBounds as t_RangeBounds}

include Core_models.Bundle {f_start_bound_pre as f_start_bound_pre}

include Core_models.Bundle {f_start_bound_post as f_start_bound_post}

include Core_models.Bundle {f_start_bound as f_start_bound}

include Core_models.Bundle {f_end_bound_pre as f_end_bound_pre}

include Core_models.Bundle {f_end_bound_post as f_end_bound_post}

include Core_models.Bundle {f_end_bound as f_end_bound}

include Core_models.Bundle {f_contains_pre as f_contains_pre}

include Core_models.Bundle {f_contains_post as f_contains_post}

include Core_models.Bundle {f_contains as f_contains}

include Core_models.Bundle {bounds_contain as bounds_contain}

include Core_models.Bundle {impl__from__range as impl}

include Core_models.Bundle {impl_1__from__range as impl_1}

include Core_models.Bundle {impl_2__from__range as impl_2}

include Core_models.Bundle {impl_3__from__range as impl_3}

include Core_models.Bundle {impl_4__from__range as impl_4}

include Core_models.Bundle {bound_as_ref as bound_as_ref}

include Core_models.Bundle {impl_5 as impl_5}

include Core_models.Bundle {impl_6__from__range as impl_6}

include Core_models.Bundle {impl_7__new as impl_7__new}

include Core_models.Bundle {impl_7__start as impl_7__start}

include Core_models.Bundle {impl_7__end as impl_7__end}

include Core_models.Bundle {impl_7__into_inner as impl_7__into_inner}

include Core_models.Bundle {impl_10__contains as impl_10__contains}

include Core_models.Bundle {impl_10__is_empty as impl_10__is_empty}
