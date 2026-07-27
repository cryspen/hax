module New_tests.Legacy__cyclic_modules__lib.Issue_1823_.First_example.Bundle
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_A = | A : t_A

type t_B = | B : t_B

let impl__mkb (self: t_A) : t_B = B <: t_B

let impl__mka (self: t_B) : t_A = A <: t_A
