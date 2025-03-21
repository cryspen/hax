
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

(* From Core Require Import Core. *)

From Core Require Import Core_Clone (t_Clone).
Export Core_Clone (t_Clone).

Class t_Copy (v_Self : Type) `{t_Clone (v_Self)} : Type :=
  {
  }.
Arguments t_Copy (_) {_}.

Class t_Destruct (v_Self : Type) : Type :=
  {
  }.
Arguments t_Destruct (_).

Class t_Sized (v_Self : Type) : Type :=
  {
  }.
Arguments t_Sized (_).

Record t_PhantomData (v_T : Type) `{t_Sized (v_T)} : Type :=
  {
  }.
Arguments Build_t_PhantomData {_} {_}.
#[export]
Notation "'PhantomData'" := Build_t_PhantomData.

Class t_Tuple (v_Self : Type) : Type :=
  {
  }.
Arguments t_Tuple (_).

#[global] Instance t_Sized_any T : t_Sized T := {}.
