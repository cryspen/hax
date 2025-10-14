module Hax_lib.Int
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

include Hax_lib.Bundle {t_Int as t_Int}

include Hax_lib.Bundle {Int as Int}

include Hax_lib.Bundle {impl_8 as impl_8}

include Hax_lib.Bundle {impl_9 as impl_9}

include Hax_lib.Bundle {impl_10 as impl_10}

include Hax_lib.Bundle {impl_11 as impl_11}

include Hax_lib.Bundle {impl_12 as impl_12}

include Hax_lib.Bundle {impl_13 as impl_13}

include Hax_lib.Bundle {impl_14 as impl_14}

include Hax_lib.Bundle {impl_15 as impl_15}

include Hax_lib.Bundle {impl as impl}

include Hax_lib.Bundle {impl_1__new as impl_Int__new}

include Hax_lib.Bundle {impl_1__get as impl_Int__get}

include Hax_lib.Bundle {impl_2 as impl_2}

include Hax_lib.Bundle {impl_3 as impl_3}

include Hax_lib.Bundle {impl_4 as impl_4}

include Hax_lib.Bundle {impl_5 as impl_5}

include Hax_lib.Bundle {impl_6 as impl_6}

include Hax_lib.Bundle {impl_7__pow2 as impl_Int__pow2}

include Hax_lib.Bundle {impl_7__e_unsafe_from_str as impl_Int__e_unsafe_from_str}

include Hax_lib.Bundle {impl_7__rem_euclid as impl_Int__rem_euclid}

include Hax_lib.Bundle {t_ToInt as t_ToInt}

include Hax_lib.Bundle {f_to_int_pre as f_to_int_pre}

include Hax_lib.Bundle {f_to_int_post as f_to_int_post}

include Hax_lib.Bundle {f_to_int as f_to_int}

include Hax_lib.Bundle {impl_16 as impl_16}

include Hax_lib.Bundle {impl_17 as impl_ToInt_for_u8}

include Hax_lib.Bundle {impl_18 as impl_18}

include Hax_lib.Bundle {impl_19 as impl_ToInt_for_u16}

include Hax_lib.Bundle {impl_20 as impl_20}

include Hax_lib.Bundle {impl_21 as impl_ToInt_for_u32}

include Hax_lib.Bundle {impl_22 as impl_22}

include Hax_lib.Bundle {impl_23 as impl_ToInt_for_u64}

include Hax_lib.Bundle {impl_24 as impl_24}

include Hax_lib.Bundle {impl_25 as impl_ToInt_for_u128}

include Hax_lib.Bundle {impl_26 as impl_26}

include Hax_lib.Bundle {impl_27 as impl_ToInt_for_usize}

include Hax_lib.Bundle {impl_28 as impl_28}

include Hax_lib.Bundle {impl_29 as impl_ToInt_for_i8}

include Hax_lib.Bundle {impl_30 as impl_30}

include Hax_lib.Bundle {impl_31 as impl_ToInt_for_i16}

include Hax_lib.Bundle {impl_32 as impl_32}

include Hax_lib.Bundle {impl_33 as impl_ToInt_for_i32}

include Hax_lib.Bundle {impl_34 as impl_34}

include Hax_lib.Bundle {impl_35 as impl_ToInt_for_i64}

include Hax_lib.Bundle {impl_36 as impl_36}

include Hax_lib.Bundle {impl_37 as impl_ToInt_for_i128}

include Hax_lib.Bundle {impl_38 as impl_38}

include Hax_lib.Bundle {impl_39 as impl_ToInt_for_isize}

include Hax_lib.Bundle {impl_40 as impl_40}

include Hax_lib.Bundle {impl_41__to_u8 as impl_Int__to_u8}

include Hax_lib.Bundle {impl_42 as impl_42}

include Hax_lib.Bundle {impl_43__to_u16 as impl_Int__to_u16}

include Hax_lib.Bundle {impl_44 as impl_44}

include Hax_lib.Bundle {impl_45__to_u32 as impl_Int__to_u32}

include Hax_lib.Bundle {impl_46 as impl_46}

include Hax_lib.Bundle {impl_47__to_u64 as impl_Int__to_u64}

include Hax_lib.Bundle {impl_48 as impl_48}

include Hax_lib.Bundle {impl_49__to_u128 as impl_Int__to_u128}

include Hax_lib.Bundle {impl_50 as impl_50}

include Hax_lib.Bundle {impl_51__to_usize as impl_Int__to_usize}

include Hax_lib.Bundle {impl_52 as impl_52}

include Hax_lib.Bundle {impl_53__to_i8 as impl_Int__to_i8}

include Hax_lib.Bundle {impl_54 as impl_54}

include Hax_lib.Bundle {impl_55__to_i16 as impl_Int__to_i16}

include Hax_lib.Bundle {impl_56 as impl_56}

include Hax_lib.Bundle {impl_57__to_i32 as impl_Int__to_i32}

include Hax_lib.Bundle {impl_58 as impl_58}

include Hax_lib.Bundle {impl_59__to_i64 as impl_Int__to_i64}

include Hax_lib.Bundle {impl_60 as impl_60}

include Hax_lib.Bundle {impl_61__to_i128 as impl_Int__to_i128}

include Hax_lib.Bundle {impl_62 as impl_62}

include Hax_lib.Bundle {impl_63__to_isize as impl_Int__to_isize}
