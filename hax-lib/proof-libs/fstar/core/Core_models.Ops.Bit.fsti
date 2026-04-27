module Core_models.Ops.Bit
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::ops::ShrAssign`]
class t_ShrAssign (v_Self: Type0) (v_Rhs: Type0) = {
  f_shr_assign_pre:v_Self -> v_Rhs -> Type0;
  f_shr_assign_post:v_Self -> v_Rhs -> v_Self -> Type0;
  f_shr_assign:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure v_Self (f_shr_assign_pre x0 x1) (fun result -> f_shr_assign_post x0 x1 result)
}

/// See [`std::ops::ShlAssign`]
class t_ShlAssign (v_Self: Type0) (v_Rhs: Type0) = {
  f_shl_assign_pre:v_Self -> v_Rhs -> Type0;
  f_shl_assign_post:v_Self -> v_Rhs -> v_Self -> Type0;
  f_shl_assign:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure v_Self (f_shl_assign_pre x0 x1) (fun result -> f_shl_assign_post x0 x1 result)
}

/// See [`std::ops::BitXorAssign`]
class t_BitXorAssign (v_Self: Type0) (v_Rhs: Type0) = {
  f_bitxor_assign_pre:v_Self -> v_Rhs -> Type0;
  f_bitxor_assign_post:v_Self -> v_Rhs -> v_Self -> Type0;
  f_bitxor_assign:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure v_Self
        (f_bitxor_assign_pre x0 x1)
        (fun result -> f_bitxor_assign_post x0 x1 result)
}

/// See [`std::ops::BitAndAssign`]
class t_BitAndAssign (v_Self: Type0) (v_Rhs: Type0) = {
  f_bitand_assign_pre:v_Self -> v_Rhs -> Type0;
  f_bitand_assign_post:v_Self -> v_Rhs -> v_Self -> Type0;
  f_bitand_assign:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure v_Self
        (f_bitand_assign_pre x0 x1)
        (fun result -> f_bitand_assign_post x0 x1 result)
}

/// See [`std::ops::BitOrAssign`]
class t_BitOrAssign (v_Self: Type0) (v_Rhs: Type0) = {
  f_bitor_assign_pre:v_Self -> v_Rhs -> Type0;
  f_bitor_assign_post:v_Self -> v_Rhs -> v_Self -> Type0;
  f_bitor_assign:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure v_Self (f_bitor_assign_pre x0 x1) (fun result -> f_bitor_assign_post x0 x1 result)
}

/// See [`std::ops::Shr`]
class t_Shr (v_Self: Type0) (v_Rhs: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Output:Type0;
  f_shr_pre:v_Self -> v_Rhs -> Type0;
  f_shr_post:v_Self -> v_Rhs -> f_Output -> Type0;
  f_shr:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure f_Output (f_shr_pre x0 x1) (fun result -> f_shr_post x0 x1 result)
}

/// See [`std::ops::Shl`]
class t_Shl (v_Self: Type0) (v_Rhs: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Output:Type0;
  f_shl_pre:v_Self -> v_Rhs -> Type0;
  f_shl_post:v_Self -> v_Rhs -> f_Output -> Type0;
  f_shl:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure f_Output (f_shl_pre x0 x1) (fun result -> f_shl_post x0 x1 result)
}

/// See [`std::ops::BitXor`]
class t_BitXor (v_Self: Type0) (v_Rhs: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Output:Type0;
  f_bitxor_pre:v_Self -> v_Rhs -> Type0;
  f_bitxor_post:v_Self -> v_Rhs -> f_Output -> Type0;
  f_bitxor:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure f_Output (f_bitxor_pre x0 x1) (fun result -> f_bitxor_post x0 x1 result)
}

/// See [`std::ops::BitAnd`]
class t_BitAnd (v_Self: Type0) (v_Rhs: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Output:Type0;
  f_bitand_pre:v_Self -> v_Rhs -> Type0;
  f_bitand_post:v_Self -> v_Rhs -> f_Output -> Type0;
  f_bitand:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure f_Output (f_bitand_pre x0 x1) (fun result -> f_bitand_post x0 x1 result)
}

/// See [`std::ops::BitOr`]
class t_BitOr (v_Self: Type0) (v_Rhs: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Output:Type0;
  f_bitor_pre:v_Self -> v_Rhs -> Type0;
  f_bitor_post:v_Self -> v_Rhs -> f_Output -> Type0;
  f_bitor:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure f_Output (f_bitor_pre x0 x1) (fun result -> f_bitor_post x0 x1 result)
}

/// See [`std::ops::Not`]
class t_Not (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Output:Type0;
  f_not_pre:v_Self -> Type0;
  f_not_post:v_Self -> f_Output -> Type0;
  f_not:x0: v_Self -> Prims.Pure f_Output (f_not_pre x0) (fun result -> f_not_post x0 result)
}
