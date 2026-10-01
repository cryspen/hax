module Alloc.Alloc
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

class t_Allocator (v_Self: Type0) = { __marker_trait_t_Allocator:Prims.unit }

type t_Global = | Global : t_Global

let impl_1: Core_models.Clone.t_Clone t_Global =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_Allocator t_Global = { __marker_trait_t_Allocator = () }
