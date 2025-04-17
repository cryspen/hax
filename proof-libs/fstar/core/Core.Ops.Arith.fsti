module Core.Ops.Arith
open Rust_primitives
open Hax_lib.Prop

class t_Add self rhs = {
   [@@@ Tactics.Typeclasses.no_method]
   f_Output: Type;
   f_add_pre: self -> rhs -> t_Prop;
   f_add_post: self -> rhs -> f_Output -> t_Prop;
   f_add: x:self -> y:rhs -> Pure f_Output (f_add_pre x y) (fun r -> f_add_post x y r);
}

class t_Sub self rhs = {
   [@@@ Tactics.Typeclasses.no_method]
   f_Output: Type;
   f_sub_pre: self -> rhs -> t_Prop;
   f_sub_post: self -> rhs -> f_Output -> t_Prop;
   f_sub: x:self -> y:rhs -> Pure f_Output (f_sub_pre x y) (fun r -> f_sub_post x y r);
}

class t_Mul self rhs = {
   [@@@ Tactics.Typeclasses.no_method]
   f_Output: Type;
   f_mul_pre: self -> rhs -> t_Prop;
   f_mul_post: self -> rhs -> f_Output -> t_Prop;
   f_mul: x:self -> y:rhs -> Pure f_Output (f_mul_pre x y) (fun r -> f_mul_post x y r);
}

class t_Div self rhs = {
   [@@@ Tactics.Typeclasses.no_method]
   f_Output: Type;
   f_div_pre: self -> rhs -> t_Prop;
   f_div_post: self -> rhs -> f_Output -> t_Prop;
   f_div: x:self -> y:rhs -> Pure f_Output (f_div_pre x y) (fun r -> f_div_post x y r);
}

class t_AddAssign self rhs = {
  f_add_assign_pre: self -> rhs -> t_Prop;
  f_add_assign_post: self -> rhs -> self -> t_Prop;
  f_add_assign: x:self -> y:rhs -> Pure self (f_add_assign_pre x y) (fun r -> f_add_assign_post x y r);
}

class t_SubAssign self rhs = {
  f_sub_assign_pre: self -> rhs -> t_Prop;
  f_sub_assign_post: self -> rhs -> self -> t_Prop;
  f_sub_assign: x:self -> y:rhs -> Pure self (f_sub_assign_pre x y) (fun r -> f_sub_assign_post x y r);
}

class t_MulAssign self rhs = {
   f_mul_assign_pre: self -> rhs -> t_Prop;
   f_mul_assign_post: self -> rhs -> self -> t_Prop;
   f_mul_assign: x:self -> y:rhs -> Pure self (f_mul_assign_pre x y) (fun r -> f_mul_assign_post x y r);
}

class t_DivAssign self rhs = {
   f_div_assign_pre: self -> rhs -> t_Prop;
   f_div_assign_post: self -> rhs -> self -> t_Prop;
   f_div_assign: x:self -> y:rhs -> Pure self (f_div_assign_pre x y) (fun r -> f_div_assign_post x y r);
}

let f_neg #t x = zero #t -! x
