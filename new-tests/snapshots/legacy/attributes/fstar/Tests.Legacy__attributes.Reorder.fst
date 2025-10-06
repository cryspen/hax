module Tests.Legacy__attributes.Reorder
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_Foo = {
  f_field_3_:u8;
  f_field_4_:u8;
  f_field_2_:u8;
  f_field_1_:u8
}

type t_Bar =
  | Bar_A {
    f_a_field_3_:u8;
    f_a_field_1_:u8;
    f_a_field_2_:u8
  }: t_Bar
  | Bar_B {
    f_b_field_1_:u8;
    f_b_field_3_:u8;
    f_b_field_2_:u8
  }: t_Bar
