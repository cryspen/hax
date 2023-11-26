module Core.Ops
open Rust_primitives

open LowStar.BufferOps
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

// class add_tc self rhs = {
//   output: Type;
//   in_bounds: self -> rhs -> Type0;
//   ( +! ): x:self -> y:rhs {in_bounds x y} -> output;
// }

inline_for_extraction
class negation_tc self = {
  ( ~. ): self -> self;
}

inline_for_extraction
instance negation_for_integers #t: negation_tc (int_t t) = {
  ( ~. ) = fun x -> lognot x
}

inline_for_extraction
instance negation_for_bool: negation_tc bool = {
  ( ~. ) = not
}

open Core.Ops.Index

inline_for_extraction
let ( .[] ) #self #idx {| inst: t_Index self idx |}
  : s:self -> i:idx{in_range s i} -> HST.St inst.f_Output
  = f_index

