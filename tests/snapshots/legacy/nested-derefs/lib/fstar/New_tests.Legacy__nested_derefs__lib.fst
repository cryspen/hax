module New_tests.Legacy__nested_derefs__lib
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core_models

let f (x: usize) : usize = x

let g (x: usize) : usize = f x
