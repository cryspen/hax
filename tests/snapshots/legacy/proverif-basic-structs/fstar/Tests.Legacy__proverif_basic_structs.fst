module Tests.Legacy__proverif_basic_structs
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_Ainitial = { f_x:u8 }

type t_A = {
  f_one:usize;
  f_two:usize
}

type t_B = | B : usize -> t_B
