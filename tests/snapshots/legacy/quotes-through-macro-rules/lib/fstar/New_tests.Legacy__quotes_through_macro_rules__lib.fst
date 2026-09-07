module New_tests.Legacy__quotes_through_macro_rules__lib
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core_models

let antiquotes_through_wrappers (x: u32) : u32 =
  let y:u32 = x in
  let _:Prims.unit = assert (x == y) in
  let _:Prims.unit = assert (x == y) in
  let _:Prims.unit = assert (x == y) in
  y
