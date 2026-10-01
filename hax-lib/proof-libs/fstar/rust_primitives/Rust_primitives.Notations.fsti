module Rust_primitives.Notations
open Rust_primitives

open Core_models.Ops.Index

let ( .[] ) #self #idx {| inst: t_Index self idx |}
  (s:self) (i:idx{f_index_pre s i}): inst.f_Output
  = f_index s i
