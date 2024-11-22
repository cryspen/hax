(* File automatically generated by Hacspec *)
From Hacspec Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.

Require Import num.
Export num.

Require Import u8.
Export u8.

Require Import u16.
Export u16.

Require Import u32.
Export u32.

Require Import u64.
Export u64.

Require Import u128.
Export u128.

Require Import usize.
Export usize.

(*Not implemented yet? todo(item)*)

(*item error backend*)

Class t_Step := {
  f_steps_between : (Self -> Self -> t_Option_t t_usize_t) ;
  f_forward_checked : (Self -> t_usize_t -> t_Option_t Self) ;
}.

(*item error backend*)

(*item error backend*)

#[global] Instance t_u8_t_t_Step : t_Step t_u8_t := {
  f_steps_between (start : t_u8_t) (end : t_u8_t) := if start<=.?end
  then Option_Some (f_into ((f_clone end).-(f_clone start)))
  else Option_Nonet_Option_t t_usize_t;
  f_forward_checked (start : t_u8_t) (n : t_usize_t) := match f_try_from n with
  | Result_Ok n =>
    impl_6__checked_add start n
  | Result_Err _ =>
    Option_Nonet_Option_t t_u8_t
  end;
}.

#[global] Instance t_u16_t_t_Step : t_Step t_u16_t := {
  f_steps_between (start : t_u16_t) (end : t_u16_t) := if start<=.?end
  then Option_Some (f_into ((f_clone end).-(f_clone start)))
  else Option_Nonet_Option_t t_usize_t;
  f_forward_checked (start : t_u16_t) (n : t_usize_t) := match f_try_from n with
  | Result_Ok n =>
    impl_7__checked_add start n
  | Result_Err _ =>
    Option_Nonet_Option_t t_u16_t
  end;
}.

#[global] Instance t_u32_t_t_Step : t_Step t_u32_t := {
  f_steps_between (start : t_u32_t) (end : t_u32_t) := if start<=.?end
  then Option_Some (f_into ((f_clone end).-(f_clone start)))
  else Option_Nonet_Option_t t_usize_t;
  f_forward_checked (start : t_u32_t) (n : t_usize_t) := match f_try_from n with
  | Result_Ok n =>
    impl_8__checked_add start n
  | Result_Err _ =>
    Option_Nonet_Option_t t_u32_t
  end;
}.

#[global] Instance t_u64_t_t_Step : t_Step t_u64_t := {
  f_steps_between (start : t_u64_t) (end : t_u64_t) := if start<=.?end
  then Option_Some (f_into ((f_clone end).-(f_clone start)))
  else Option_Nonet_Option_t t_usize_t;
  f_forward_checked (start : t_u64_t) (n : t_usize_t) := match f_try_from n with
  | Result_Ok n =>
    impl_9__checked_add start n
  | Result_Err _ =>
    Option_Nonet_Option_t t_u64_t
  end;
}.

#[global] Instance t_u128_t_t_Step : t_Step t_u128_t := {
  f_steps_between (start : t_u128_t) (end : t_u128_t) := if start<=.?end
  then impl__ok (f_try_from ((f_clone end).-(f_clone start)))
  else Option_Nonet_Option_t t_usize_t;
  f_forward_checked (start : t_u128_t) (n : t_usize_t) := Option_Nonet_Option_t t_u128_t;
}.

#[global] Instance t_usize_t_t_Step : t_Step t_usize_t := {
  f_steps_between (start : t_usize_t) (end : t_usize_t) := if start<=.?end
  then Option_Some (f_into ((f_clone end).-(f_clone start)))
  else Option_Nonet_Option_t t_usize_t;
  f_forward_checked (start : t_usize_t) (n : t_usize_t) := match f_try_from n with
  | Result_Ok n =>
    impl_11__checked_add start n
  | Result_Err _ =>
    Option_Nonet_Option_t t_usize_t
  end;
}.
