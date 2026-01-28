module Core_models.Ops.Arith
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

class t_AddAssign (v_Self: Type0) (v_Rhs: Type0) = {
  f_add_assign_pre:v_Self -> v_Rhs -> Type0;
  f_add_assign_post:v_Self -> v_Rhs -> v_Self -> Type0;
  f_add_assign:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure v_Self (f_add_assign_pre x0 x1) (fun result -> f_add_assign_post x0 x1 result)
}

class t_SubAssign (v_Self: Type0) (v_Rhs: Type0) = {
  f_sub_assign_pre:v_Self -> v_Rhs -> Type0;
  f_sub_assign_post:v_Self -> v_Rhs -> v_Self -> Type0;
  f_sub_assign:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure v_Self (f_sub_assign_pre x0 x1) (fun result -> f_sub_assign_post x0 x1 result)
}

class t_MulAssign (v_Self: Type0) (v_Rhs: Type0) = {
  f_mul_assign_pre:v_Self -> v_Rhs -> Type0;
  f_mul_assign_post:v_Self -> v_Rhs -> v_Self -> Type0;
  f_mul_assign:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure v_Self (f_mul_assign_pre x0 x1) (fun result -> f_mul_assign_post x0 x1 result)
}

class t_DivAssign (v_Self: Type0) (v_Rhs: Type0) = {
  f_div_assign_pre:v_Self -> v_Rhs -> Type0;
  f_div_assign_post:v_Self -> v_Rhs -> v_Self -> Type0;
  f_div_assign:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure v_Self (f_div_assign_pre x0 x1) (fun result -> f_div_assign_post x0 x1 result)
}

class t_RemAssign (v_Self: Type0) (v_Rhs: Type0) = {
  f_rem_assign_pre:v_Self -> v_Rhs -> Type0;
  f_rem_assign_post:v_Self -> v_Rhs -> v_Self -> Type0;
  f_rem_assign:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure v_Self (f_rem_assign_pre x0 x1) (fun result -> f_rem_assign_post x0 x1 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl:t_AddAssign u8 u8

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_1:t_SubAssign u8 u8

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_2:t_AddAssign u16 u16

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_3:t_SubAssign u16 u16

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_4:t_AddAssign u32 u32

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_5:t_SubAssign u32 u32

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_6:t_AddAssign u64 u64

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_7:t_SubAssign u64 u64

class t_Add (v_Self: Type0) (v_Rhs: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Output:Type0;
  f_add_pre:v_Self -> v_Rhs -> Type0;
  f_add_post:v_Self -> v_Rhs -> f_Output -> Type0;
  f_add:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure f_Output (f_add_pre x0 x1) (fun result -> f_add_post x0 x1 result)
}

class t_Sub (v_Self: Type0) (v_Rhs: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Output:Type0;
  f_sub_pre:v_Self -> v_Rhs -> Type0;
  f_sub_post:v_Self -> v_Rhs -> f_Output -> Type0;
  f_sub:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure f_Output (f_sub_pre x0 x1) (fun result -> f_sub_post x0 x1 result)
}

class t_Mul (v_Self: Type0) (v_Rhs: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Output:Type0;
  f_mul_pre:v_Self -> v_Rhs -> Type0;
  f_mul_post:v_Self -> v_Rhs -> f_Output -> Type0;
  f_mul:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure f_Output (f_mul_pre x0 x1) (fun result -> f_mul_post x0 x1 result)
}

class t_Div (v_Self: Type0) (v_Rhs: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Output:Type0;
  f_div_pre:v_Self -> v_Rhs -> Type0;
  f_div_post:v_Self -> v_Rhs -> f_Output -> Type0;
  f_div:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure f_Output (f_div_pre x0 x1) (fun result -> f_div_post x0 x1 result)
}

class t_Neg (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Output:Type0;
  f_neg_pre:v_Self -> Type0;
  f_neg_post:v_Self -> f_Output -> Type0;
  f_neg:x0: v_Self -> Prims.Pure f_Output (f_neg_pre x0) (fun result -> f_neg_post x0 result)
}

class t_Rem (v_Self: Type0) (v_Rhs: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Output:Type0;
  f_rem_pre:v_Self -> v_Rhs -> Type0;
  f_rem_post:v_Self -> v_Rhs -> f_Output -> Type0;
  f_rem:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure f_Output (f_rem_pre x0 x1) (fun result -> f_rem_post x0 x1 result)
}
