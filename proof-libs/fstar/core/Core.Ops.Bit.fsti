module Core.Ops.Bit
open FStar.Mul

class t_Shr (v_Self: Type0) (v_Rhs: Type0) = {
  f_Output:Type0;
}

class t_BitXor self rhs = {
  [@@@ Tactics.Typeclasses.no_method]
  f_Output: Type;
  f_bitxor_pre: self -> rhs -> bool;
  f_bitxor_post: self -> rhs -> f_Output -> bool;
  f_bitxor: x:self -> y:rhs -> Pure f_Output (f_bitxor_pre x y) (fun r -> f_bitxor_post x y r);
}

class t_BitAnd self rhs = {
  [@@@ Tactics.Typeclasses.no_method]
  f_Output: Type;
  f_bitand_pre: self -> rhs -> bool;
  f_bitand_post: self -> rhs -> f_Output -> bool;
  f_bitand: x:self -> y:rhs -> Pure f_Output (f_bitand_pre x y) (fun r -> f_bitand_post x y r);
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_bitxor_bool: Core.Ops.Bit.t_BitXor Prims.bool Prims.bool =
  {
    f_Output = Prims.bool;
    f_bitxor_pre = (fun (self: Prims.bool) (rhs: Prims.bool) -> true);
    f_bitxor_post = (fun (self: Prims.bool) (rhs: Prims.bool) (out: Prims.bool) -> (self <> rhs) = out );
    f_bitxor = fun (self: Prims.bool) (rhs: Prims.bool) -> (self <> rhs) <: Prims.bool
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_bitand_bool: Core.Ops.Bit.t_BitAnd Prims.bool Prims.bool =
  {
    f_Output = Prims.bool;
    f_bitand_pre = (fun (self: Prims.bool) (rhs: Prims.bool) -> true);
    f_bitand_post = (fun (self: Prims.bool) (rhs: Prims.bool) (out: Prims.bool) -> (self && rhs) = out );
    f_bitand = fun (self: Prims.bool) (rhs: Prims.bool) -> (self && rhs) <: Prims.bool
  }
