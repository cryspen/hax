(* File automatically generated by Hacspec *)
From Hacspec Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.

Require Import ops.
Export ops.

Class t_Sealed := {
}.

#[global] Instance t_RangeTo_t uint_size_t_Sealed : t_Sealed (t_RangeTo_t uint_size) := {
}.

#[global] Instance t_RangeFrom_t uint_size_t_Sealed : t_Sealed (t_RangeFrom_t uint_size) := {
}.

#[global] Instance t_RangeFull_t_t_Sealed : t_Sealed t_RangeFull_t := {
}.

#[global] Instance t_RangeInclusive_t uint_size_t_Sealed : t_Sealed (t_RangeInclusive_t uint_size) := {
}.

#[global] Instance t_RangeToInclusive_t uint_size_t_Sealed : t_Sealed (t_RangeToInclusive_t uint_size) := {
}.

#[global] Instance t_Bound_t uint_size × t_Bound_t uint_size_t_Sealed : t_Sealed (t_Bound_t uint_size × t_Bound_t uint_size) := {
}.

#[global] Instance t_Range_t uint_size_t_Sealed : t_Sealed (t_Range_t uint_size) := {
}.

#[global] Instance t_IndexRange_t_t_Sealed : t_Sealed t_IndexRange_t := {
}.

#[global] Instance t_usize_t_t_Sealed : t_Sealed t_usize_t := {
}.
