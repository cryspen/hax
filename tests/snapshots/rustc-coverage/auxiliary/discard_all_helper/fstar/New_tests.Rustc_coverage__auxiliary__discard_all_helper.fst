module New_tests.Rustc_coverage__auxiliary__discard_all_helper
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core_models

let external_function (_: Prims.unit) : Prims.unit = ()
