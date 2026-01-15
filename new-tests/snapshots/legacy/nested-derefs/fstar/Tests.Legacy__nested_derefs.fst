module Tests.Legacy__nested_derefs
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let f (x: usize) : usize = x

let g (x: usize) : usize = f x
