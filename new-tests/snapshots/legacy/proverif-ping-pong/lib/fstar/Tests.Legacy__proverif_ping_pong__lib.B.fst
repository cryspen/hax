module Tests.Legacy__proverif_ping_pong__lib.B
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_B0 = | B0 : t_B0

type t_B1 = { f_received:u8 }

type t_B1alt = | B1alt : t_B1alt

type t_B2 = | B2 : t_B2

let init_b (_: Prims.unit) : Core.Result.t_Result t_B0 Hax_lib_protocol.t_ProtocolError =
  Core.Result.Result_Ok (B0 <: t_B0) <: Core.Result.t_Result t_B0 Hax_lib_protocol.t_ProtocolError

let read_ping (e_state: t_B0) (msg: Tests.Legacy__proverif_ping_pong__lib.t_Message)
    : Core.Result.t_Result t_B1 Hax_lib_protocol.t_ProtocolError =
  match msg <: Tests.Legacy__proverif_ping_pong__lib.t_Message with
  | Tests.Legacy__proverif_ping_pong__lib.Message_Ping received ->
    Core.Result.Result_Ok ({ f_received = received } <: t_B1)
    <:
    Core.Result.t_Result t_B1 Hax_lib_protocol.t_ProtocolError
  | Tests.Legacy__proverif_ping_pong__lib.Message_Pong _ ->
    Core.Result.Result_Err
    (Hax_lib_protocol.ProtocolError_InvalidMessage <: Hax_lib_protocol.t_ProtocolError)
    <:
    Core.Result.t_Result t_B1 Hax_lib_protocol.t_ProtocolError

/// @fail(extraction): proverif(HAX0008)
let read_ping_alt (e_state: t_B0) (msg: Tests.Legacy__proverif_ping_pong__lib.t_Message)
    : Core.Result.t_Result t_B1alt Hax_lib_protocol.t_ProtocolError =
  match
    (match msg <: Tests.Legacy__proverif_ping_pong__lib.t_Message with
      | Tests.Legacy__proverif_ping_pong__lib.Message_Ping received ->
        (match received =. mk_u8 42 <: bool with
          | true ->
            Core.Option.Option_Some
            (Core.Result.Result_Ok (B1alt <: t_B1alt)
              <:
              Core.Result.t_Result t_B1alt Hax_lib_protocol.t_ProtocolError)
            <:
            Core.Option.t_Option (Core.Result.t_Result t_B1alt Hax_lib_protocol.t_ProtocolError)
          | _ ->
            Core.Option.Option_None
            <:
            Core.Option.t_Option (Core.Result.t_Result t_B1alt Hax_lib_protocol.t_ProtocolError))
      | _ ->
        Core.Option.Option_None
        <:
        Core.Option.t_Option (Core.Result.t_Result t_B1alt Hax_lib_protocol.t_ProtocolError))
    <:
    Core.Option.t_Option (Core.Result.t_Result t_B1alt Hax_lib_protocol.t_ProtocolError)
  with
  | Core.Option.Option_Some x -> x
  | Core.Option.Option_None  ->
    Core.Result.Result_Err
    (Hax_lib_protocol.ProtocolError_InvalidMessage <: Hax_lib_protocol.t_ProtocolError)
    <:
    Core.Result.t_Result t_B1alt Hax_lib_protocol.t_ProtocolError

let write_pong (state: t_B1)
    : Core.Result.t_Result (t_B2 & Tests.Legacy__proverif_ping_pong__lib.t_Message)
      Hax_lib_protocol.t_ProtocolError =
  Core.Result.Result_Ok
  ((B2 <: t_B2),
    (Tests.Legacy__proverif_ping_pong__lib.Message_Pong state.f_received
      <:
      Tests.Legacy__proverif_ping_pong__lib.t_Message)
    <:
    (t_B2 & Tests.Legacy__proverif_ping_pong__lib.t_Message))
  <:
  Core.Result.t_Result (t_B2 & Tests.Legacy__proverif_ping_pong__lib.t_Message)
    Hax_lib_protocol.t_ProtocolError
