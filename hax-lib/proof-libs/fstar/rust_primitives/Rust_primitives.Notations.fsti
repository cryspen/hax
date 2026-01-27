module Rust_primitives.Notations
open Rust_primitives

class negation_tc self = {
  ( ~. ): self -> self;
}

instance negation_for_integers #t: negation_tc (int_t t) = {
  ( ~. ) = fun x -> lognot x
}

instance negation_for_bool: negation_tc bool = {
  ( ~. ) = not
}

open Core_models.Ops.Index

let ( .[] ) #self #idx {| inst: t_Index self idx |}
  (s:self) (i:idx{f_index_pre s i}): inst.f_Output
  = f_index s i
