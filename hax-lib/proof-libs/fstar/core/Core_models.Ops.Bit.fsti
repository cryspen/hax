module Core_models.Ops.Bit
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul

class t_Shr (v_Self: Type0) (v_Rhs: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Output:Type0;
  f_shr_pre:v_Self -> v_Rhs -> Type0;
  f_shr_post:v_Self -> v_Rhs -> f_Output -> Type0;
  f_shr:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure f_Output (f_shr_pre x0 x1) (fun result -> f_shr_post x0 x1 result)
}

class t_BitXor (v_Self: Type0) (v_Rhs: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Output:Type0;
  f_bitxor_pre:v_Self -> v_Rhs -> Type0;
  f_bitxor_post:v_Self -> v_Rhs -> f_Output -> Type0;
  f_bitxor:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure f_Output (f_bitxor_pre x0 x1) (fun result -> f_bitxor_post x0 x1 result)
}

class t_BitAnd (v_Self: Type0) (v_Rhs: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Output:Type0;
  f_bitand_pre:v_Self -> v_Rhs -> Type0;
  f_bitand_post:v_Self -> v_Rhs -> f_Output -> Type0;
  f_bitand:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure f_Output (f_bitand_pre x0 x1) (fun result -> f_bitand_post x0 x1 result)
}
