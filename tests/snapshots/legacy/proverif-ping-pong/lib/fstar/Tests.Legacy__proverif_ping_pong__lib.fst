module Tests.Legacy__proverif_ping_pong__lib
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_Message =
  | Message_Ping : u8 -> t_Message
  | Message_Pong : u8 -> t_Message
