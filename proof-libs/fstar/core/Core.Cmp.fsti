module Core.Cmp
open Rust_primitives

class min_tc t = {
  min: t -> t -> t
}

instance min_inttype (#t:inttype): min_tc (int_t t) = {
  min = fun a b -> if a <. b then a else b
}

class t_PartialEq (v_Self: Type) (v_Rhs: Type) = {
  // __constraint_1069563329_t_PartialEq:t_PartialEq v_Self v_Rhs;
  f_eq_pre: v_Self -> v_Rhs -> Type0;
  f_eq_post: v_Self -> v_Rhs -> bool -> Type0;
  f_eq:v_Self -> v_Rhs -> bool;
}

class t_Eq (v_Self: Type) = {
  [@@@FStar.Tactics.Typeclasses.tcresolve]
  __constraint_t_Eq_t_PartialEq:t_PartialEq v_Self v_Self;
}

type t_Ordering =
  | Ordering_Less : t_Ordering
  | Ordering_Equal : t_Ordering
  | Ordering_Greater : t_Ordering


class t_PartialOrd (v_Self: Type) (v_Rhs:Type) = {
  _super_7951719793721949255: t_PartialEq v_Self v_Rhs;
  f_partial_cmp_pre: v_Self -> v_Rhs -> Type0;
  f_partial_cmp_post: v_Self -> v_Rhs -> Core.Option.t_Option t_Ordering -> Type0;
  f_partial_cmp:v_Self -> v_Rhs -> Core.Option.t_Option t_Ordering;

  f_ge_pre: v_Self -> v_Rhs -> Type0;
  f_ge_post: v_Self -> v_Rhs -> Type0;
  f_ge: v_Self -> v_Rhs -> bool;

  f_gt_pre: v_Self -> v_Rhs -> Type0;
  f_gt_post: v_Self -> v_Rhs -> Type0;
  f_gt: v_Self -> v_Rhs -> bool;

  f_le_pre: v_Self -> v_Rhs -> Type0;
  f_le_post: v_Self -> v_Rhs -> Type0;
  f_le: v_Self -> v_Rhs -> bool;

  f_lt_pre: v_Self -> v_Rhs -> Type0;
  f_lt_post: v_Self -> v_Rhs -> Type0;
  f_lt: v_Self -> v_Rhs -> bool;
}

class t_Ord (v_Self: Type) = {
  _super_641474646876120386: t_Eq v_Self;
  _super_12012119932897234219: t_PartialOrd v_Self v_Self;
  f_cmp_pre: v_Self -> v_Self -> Type0;
  f_cmp_post: v_Self -> v_Self -> t_Ordering -> Type0;
  f_cmp:v_Self -> v_Self -> t_Ordering;
  // f_max:v_Self -> v_Self -> v_Self;
  // f_min:v_Self -> v_Self -> v_Self;
  // f_clamp:v_Self -> v_Self -> v_Self -> v_Self
}

instance all_eq (a: eqtype): t_PartialEq a a = {
  f_eq_pre = (fun x y -> True);
  f_eq_post = (fun x y r -> True);
  f_eq = (fun x y -> x = y);
}

type t_Reverse t = | Reverse of t

let impl__then x y = x

[@FStar.Tactics.Typeclasses.tcinstance]
val ord_int t: t_Ord (int_t t)

[@FStar.Tactics.Typeclasses.tcinstance]
val ord_reverse t {| t_Ord t |}: t_Ord (t_Reverse t)

[@FStar.Tactics.Typeclasses.tcinstance]
val partialOrdFloat : t_PartialOrd float float
