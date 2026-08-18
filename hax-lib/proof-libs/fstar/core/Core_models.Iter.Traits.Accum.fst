module Core_models.Iter.Traits.Accum
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::iter::Sum`]
class t_Sum (v_Self: Type0) (v_A: Type0) = {
  f_sum_pre:
      #v_I: Type0 ->
      {| i1: Core_models.Iter.Traits.Iterator.t_Iterator v_I |} ->
      #_: unit{i1.Core_models.Iter.Traits.Iterator.f_Item == v_A} ->
      v_I
    -> Type0;
  f_sum_post:
      #v_I: Type0 ->
      {| i1: Core_models.Iter.Traits.Iterator.t_Iterator v_I |} ->
      #_: unit{i1.Core_models.Iter.Traits.Iterator.f_Item == v_A} ->
      v_I ->
      v_Self
    -> Type0;
  f_sum:
      #v_I: Type0 ->
      {| i1: Core_models.Iter.Traits.Iterator.t_Iterator v_I |} ->
      #_: unit{i1.Core_models.Iter.Traits.Iterator.f_Item == v_A} ->
      x0: v_I
    -> Prims.Pure v_Self (f_sum_pre #v_I #i1 #_ x0) (fun result -> f_sum_post #v_I #i1 #_ x0 result)
}

/// See [`std::iter::Product`]
class t_Product (v_Self: Type0) (v_A: Type0) = {
  f_product_pre:
      #v_I: Type0 ->
      {| i1: Core_models.Iter.Traits.Iterator.t_Iterator v_I |} ->
      #_: unit{i1.Core_models.Iter.Traits.Iterator.f_Item == v_A} ->
      v_I
    -> Type0;
  f_product_post:
      #v_I: Type0 ->
      {| i1: Core_models.Iter.Traits.Iterator.t_Iterator v_I |} ->
      #_: unit{i1.Core_models.Iter.Traits.Iterator.f_Item == v_A} ->
      v_I ->
      v_Self
    -> Type0;
  f_product:
      #v_I: Type0 ->
      {| i1: Core_models.Iter.Traits.Iterator.t_Iterator v_I |} ->
      #_: unit{i1.Core_models.Iter.Traits.Iterator.f_Item == v_A} ->
      x0: v_I
    -> Prims.Pure v_Self
        (f_product_pre #v_I #i1 #_ x0)
        (fun result -> f_product_post #v_I #i1 #_ x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl': t_Sum u8 u8

unfold
let impl = impl'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': t_Product u8 u8

unfold
let impl_1 = impl_1'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2': t_Sum u16 u16

unfold
let impl_2 = impl_2'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': t_Product u16 u16

unfold
let impl_3 = impl_3'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_4': t_Sum u32 u32

unfold
let impl_4 = impl_4'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_5': t_Product u32 u32

unfold
let impl_5 = impl_5'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_6': t_Sum u64 u64

unfold
let impl_6 = impl_6'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_7': t_Product u64 u64

unfold
let impl_7 = impl_7'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_8': t_Sum u128 u128

unfold
let impl_8 = impl_8'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_9': t_Product u128 u128

unfold
let impl_9 = impl_9'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_10': t_Sum usize usize

unfold
let impl_10 = impl_10'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_11': t_Product usize usize

unfold
let impl_11 = impl_11'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_12': t_Sum i8 i8

unfold
let impl_12 = impl_12'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_13': t_Product i8 i8

unfold
let impl_13 = impl_13'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_14': t_Sum i16 i16

unfold
let impl_14 = impl_14'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_15': t_Product i16 i16

unfold
let impl_15 = impl_15'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_16': t_Sum i32 i32

unfold
let impl_16 = impl_16'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_17': t_Product i32 i32

unfold
let impl_17 = impl_17'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_18': t_Sum i64 i64

unfold
let impl_18 = impl_18'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_19': t_Product i64 i64

unfold
let impl_19 = impl_19'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_20': t_Sum i128 i128

unfold
let impl_20 = impl_20'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_21': t_Product i128 i128

unfold
let impl_21 = impl_21'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_22': t_Sum isize isize

unfold
let impl_22 = impl_22'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_23': t_Product isize isize

unfold
let impl_23 = impl_23'
