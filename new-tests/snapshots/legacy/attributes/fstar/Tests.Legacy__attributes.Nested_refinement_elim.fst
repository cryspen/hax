module Tests.Legacy__attributes.Nested_refinement_elim
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let t_DummyRefinement = x: u16{true}

let elim_twice (x: t_DummyRefinement) : u16 = ((x <: u16) <: t_DummyRefinement) <: u16
