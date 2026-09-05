module New_tests.Legacy__proverif_minimal__lib
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core_models

let add (left right: usize) : usize = left +! right
