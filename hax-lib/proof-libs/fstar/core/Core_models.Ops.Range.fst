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

include Core_models.Bundle {impl__from__range as impl}

include Core_models.Bundle {impl_1__from__range as impl_1}

include Core_models.Bundle {impl_2__from__range as impl_2}

include Core_models.Bundle {impl_3__from__range as impl_3}

include Core_models.Bundle {impl_4__from__range as impl_4}

include Core_models.Bundle {impl_5__from__range as impl_5}

include Core_models.Bundle {impl_6__from__range as impl_6}

include Core_models.Bundle {impl_7__from__range as impl_7}

include Core_models.Bundle {impl_8__from__range as impl_8}

include Core_models.Bundle {impl_9__from__range as impl_9}

include Core_models.Bundle {impl_10__from__range as impl_10}

include Core_models.Bundle {impl_11__from__range as impl_11}
