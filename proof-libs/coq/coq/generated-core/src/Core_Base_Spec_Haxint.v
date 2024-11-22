(* File automatically generated by Hacspec *)
From Hacspec Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.

Record t_HaxInt : Type := {
  f_v : t_Cow_t (seq int8);
}.

Definition v_HaxInt_ONE : t_HaxInt_t :=
  Build_HaxInt (f_v := Cow_Borrowed (unsize (array_from_list [(@repr WORDSIZE8 1)]))).

Definition v_HaxInt_TWO : t_HaxInt_t :=
  Build_HaxInt (f_v := Cow_Borrowed (unsize (array_from_list [(@repr WORDSIZE8 2)]))).

Definition v_HaxInt_ZERO : t_HaxInt_t :=
  Build_HaxInt (f_v := Cow_Borrowed (unsize !TODO empty array!)).

#[global] Instance t_HaxInt_t_t_Clone : t_Clone t_HaxInt_t := {
  f_clone (self : t_HaxInt_t) := never_to_any (panic_fmt (impl_2__new_v1 (array_from_list [not yet implemented: specification needed]) (impl_1__none tt)));
}.

Definition div2 (s : t_HaxInt_t) : t_HaxInt_t :=
  never_to_any (panic_fmt (impl_2__new_v1 (array_from_list [not yet implemented: specification needed]) (impl_1__none tt))).

Definition is_zero (s : t_HaxInt_t) : bool :=
  never_to_any (panic_fmt (impl_2__new_v1 (array_from_list [not yet implemented: specification needed]) (impl_1__none tt))).
