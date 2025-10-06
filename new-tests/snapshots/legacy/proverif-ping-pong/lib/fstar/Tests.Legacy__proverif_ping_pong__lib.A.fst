module Tests.Legacy__proverif_ping_pong__lib.A
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_A0 = { f_data:u8 }

type t_A1 = | A1 : t_A1

type t_A2 = { f_received:u8 }

let init_a (prologue: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
    : Core.Result.t_Result t_A0 Hax_lib_protocol.t_ProtocolError =
  if (Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global prologue <: usize) <. mk_usize 1
  then
    Core.Result.Result_Err
    (Hax_lib_protocol.ProtocolError_InvalidPrologue <: Hax_lib_protocol.t_ProtocolError)
    <:
    Core.Result.t_Result t_A0 Hax_lib_protocol.t_ProtocolError
  else
    Core.Result.Result_Ok ({ f_data = prologue.[ mk_usize 0 ] } <: t_A0)
    <:
    Core.Result.t_Result t_A0 Hax_lib_protocol.t_ProtocolError

let write_ping (state: t_A0)
    : Core.Result.t_Result (t_A1 & Tests.Legacy__proverif_ping_pong__lib.t_Message)
      Hax_lib_protocol.t_ProtocolError =
  Core.Result.Result_Ok
  ((A1 <: t_A1),
    (Tests.Legacy__proverif_ping_pong__lib.Message_Ping state.f_data
      <:
      Tests.Legacy__proverif_ping_pong__lib.t_Message)
    <:
    (t_A1 & Tests.Legacy__proverif_ping_pong__lib.t_Message))
  <:
  Core.Result.t_Result (t_A1 & Tests.Legacy__proverif_ping_pong__lib.t_Message)
    Hax_lib_protocol.t_ProtocolError

let read_pong (e_state: t_A1) (msg: Tests.Legacy__proverif_ping_pong__lib.t_Message)
    : Core.Result.t_Result t_A2 Hax_lib_protocol.t_ProtocolError =
  match msg <: Tests.Legacy__proverif_ping_pong__lib.t_Message with
  | Tests.Legacy__proverif_ping_pong__lib.Message_Ping _ ->
    Core.Result.Result_Err
    (Hax_lib_protocol.ProtocolError_InvalidMessage <: Hax_lib_protocol.t_ProtocolError)
    <:
    Core.Result.t_Result t_A2 Hax_lib_protocol.t_ProtocolError
  | Tests.Legacy__proverif_ping_pong__lib.Message_Pong received ->
    Core.Result.Result_Ok ({ f_received = received } <: t_A2)
    <:
    Core.Result.t_Result t_A2 Hax_lib_protocol.t_ProtocolError
