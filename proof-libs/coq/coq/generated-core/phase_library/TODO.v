(* File automatically generated by Hacspec *)
From Coq Require Import ZArith.
Require Import List.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Require Import Ascii.
Require Import String.
Require Import Coq.Floats.Floats.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Require Import Core_Primitive.
Export Core_Primitive.

(* Array coercions *)
Coercion Build_t_Array : t_Slice >-> t_Array.
Coercion Build_t_Slice : list >-> t_Slice.

Definition unsize {A} (x : A) := x.
Definition repeat {v_T} (a : v_T) b : t_Array v_T b := List.repeat a (N.to_nat (U64_f_v (usize_0 b))).

Definition t_String := string.
Definition ToString_f_to_string (x : string) : string := x.

Definition assert (b : bool) (* `{H_assert : b = true} *) : unit := tt.
(* Inductive globality := | t_Global. *)
(* Definition t_Vec T (_ : globality) : Type := list T. *)
(* Definition impl_1__append {T} l1 l2 : list T * list T := (app l1 l2, l2). *)
(* Definition impl_1__len {A} (l : list A) := Z.of_nat (List.length l). *)
(* Definition impl__new {A} (_ : Datatypes.unit) : list A := nil. *)
(* Definition impl__with_capacity {A} (_ : Z)  : list A := nil. *)
(* Definition impl_1__push {A} l (x : A) := cons l x. *)
(* Definition impl__to_vec {T} (x : t_Slice T) : t_Vec T t_Global := {| x |}. *)
(* Definition from_elem {A} (x : A) (l : Z) := repeat x (Z.to_nat l). *)

Fixpoint build_range (l : nat) (f : nat) (a : list t_usize) : list t_usize :=
  match f with
  | 0%nat => a
  | (S n)%nat => build_range (S l) n (cons a (Build_t_usize (Build_t_U64 (unary_to_int l))))
  end.

Definition fold_range {A : Type} (l : t_usize) (u : t_usize) (_ : A -> t_usize -> bool) (x : A) (f : A -> t_usize -> A) : A := List.fold_left f (build_range (unary_from_int (U64_f_v (usize_0 l))) (unary_from_int (U64_f_v (usize_0 (Sub_f_sub u l)))) nil) x.
