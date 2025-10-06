module Tests.Legacy__proverif_minimal
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let add (left right: usize) : usize = left +! right
