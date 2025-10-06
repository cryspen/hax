
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

inductive Tests.Legacy__proverif_ping_pong__lib.Message : Type
| Ping : u8 -> Tests.Legacy__proverif_ping_pong__lib.Message 
| Pong : u8 -> Tests.Legacy__proverif_ping_pong__lib.Message 


structure Tests.Legacy__proverif_ping_pong__lib.B.B0 where


structure Tests.Legacy__proverif_ping_pong__lib.B.B1 where
  received : u8

structure Tests.Legacy__proverif_ping_pong__lib.B.B1alt where


structure Tests.Legacy__proverif_ping_pong__lib.B.B2 where


def Tests.Legacy__proverif_ping_pong__lib.B.init_b
  (_ : Rust_primitives.Hax.Tuple0)
  : Result
  (Core.Result.Result
    Tests.Legacy__proverif_ping_pong__lib.B.B0
    Hax_lib_protocol.ProtocolError)
  := do
  (Core.Result.Result.Ok Tests.Legacy__proverif_ping_pong__lib.B.B0.mk)

def Tests.Legacy__proverif_ping_pong__lib.B.read_ping
  (_state : Tests.Legacy__proverif_ping_pong__lib.B.B0)
  (msg : Tests.Legacy__proverif_ping_pong__lib.Message)
  : Result
  (Core.Result.Result
    Tests.Legacy__proverif_ping_pong__lib.B.B1
    Hax_lib_protocol.ProtocolError)
  := do
  (match msg with
    | (Tests.Legacy__proverif_ping_pong__lib.Message.Ping received)
      => do
        (Core.Result.Result.Ok
          (Tests.Legacy__proverif_ping_pong__lib.B.B1.mk
            (received := received)))
    | (Tests.Legacy__proverif_ping_pong__lib.Message.Pong _)
      => do
        (Core.Result.Result.Err Hax_lib_protocol.ProtocolError.InvalidMessage))

def Tests.Legacy__proverif_ping_pong__lib.B.read_ping_alt
  (_state : Tests.Legacy__proverif_ping_pong__lib.B.B0)
  (msg : Tests.Legacy__proverif_ping_pong__lib.Message)
  : Result
  (Core.Result.Result
    Tests.Legacy__proverif_ping_pong__lib.B.B1alt
    Hax_lib_protocol.ProtocolError)
  := do
  (match
    (match msg with
      | (Tests.Legacy__proverif_ping_pong__lib.Message.Ping received)
        => do
          (match (← Rust_primitives.Hax.Machine_int.eq received (42 : u8)) with
            | TODO_LINE_622
              => do
                (Core.Option.Option.Some
                  (Core.Result.Result.Ok
                    Tests.Legacy__proverif_ping_pong__lib.B.B1alt.mk))
            | _ => do Core.Option.Option.None)
      | _ => do Core.Option.Option.None)
  with
    | (Core.Option.Option.Some x) => do x
    | (Core.Option.Option.None )
      => do
        (Core.Result.Result.Err Hax_lib_protocol.ProtocolError.InvalidMessage))

def Tests.Legacy__proverif_ping_pong__lib.B.write_pong
  (state : Tests.Legacy__proverif_ping_pong__lib.B.B1)
  : Result
  (Core.Result.Result
    (Rust_primitives.Hax.Tuple2
      Tests.Legacy__proverif_ping_pong__lib.B.B2
      Tests.Legacy__proverif_ping_pong__lib.Message)
    Hax_lib_protocol.ProtocolError)
  := do
  (Core.Result.Result.Ok
    (Rust_primitives.Hax.Tuple2.mk
      Tests.Legacy__proverif_ping_pong__lib.B.B2.mk
      (Tests.Legacy__proverif_ping_pong__lib.Message.Pong
        (Tests.Legacy__proverif_ping_pong__lib.B.B1.received state))))

structure Tests.Legacy__proverif_ping_pong__lib.A.A0 where
  data : u8

structure Tests.Legacy__proverif_ping_pong__lib.A.A1 where


structure Tests.Legacy__proverif_ping_pong__lib.A.A2 where
  received : u8

def Tests.Legacy__proverif_ping_pong__lib.A.init_a
  (prologue : (Alloc.Vec.Vec u8 Alloc.Alloc.Global))
  : Result
  (Core.Result.Result
    Tests.Legacy__proverif_ping_pong__lib.A.A0
    Hax_lib_protocol.ProtocolError)
  := do
  (← if
  (← Rust_primitives.Hax.Machine_int.lt
      (← Alloc.Vec.Impl_1.len u8 Alloc.Alloc.Global prologue)
      (1 : usize)) then do
    (Core.Result.Result.Err Hax_lib_protocol.ProtocolError.InvalidPrologue)
  else do
    (Core.Result.Result.Ok
      (Tests.Legacy__proverif_ping_pong__lib.A.A0.mk
        (data := (← Core.Ops.Index.Index.index prologue (0 : usize))))))

def Tests.Legacy__proverif_ping_pong__lib.A.write_ping
  (state : Tests.Legacy__proverif_ping_pong__lib.A.A0)
  : Result
  (Core.Result.Result
    (Rust_primitives.Hax.Tuple2
      Tests.Legacy__proverif_ping_pong__lib.A.A1
      Tests.Legacy__proverif_ping_pong__lib.Message)
    Hax_lib_protocol.ProtocolError)
  := do
  (Core.Result.Result.Ok
    (Rust_primitives.Hax.Tuple2.mk
      Tests.Legacy__proverif_ping_pong__lib.A.A1.mk
      (Tests.Legacy__proverif_ping_pong__lib.Message.Ping
        (Tests.Legacy__proverif_ping_pong__lib.A.A0.data state))))

def Tests.Legacy__proverif_ping_pong__lib.A.read_pong
  (_state : Tests.Legacy__proverif_ping_pong__lib.A.A1)
  (msg : Tests.Legacy__proverif_ping_pong__lib.Message)
  : Result
  (Core.Result.Result
    Tests.Legacy__proverif_ping_pong__lib.A.A2
    Hax_lib_protocol.ProtocolError)
  := do
  (match msg with
    | (Tests.Legacy__proverif_ping_pong__lib.Message.Ping _)
      => do
        (Core.Result.Result.Err Hax_lib_protocol.ProtocolError.InvalidMessage)
    | (Tests.Legacy__proverif_ping_pong__lib.Message.Pong received)
      => do
        (Core.Result.Result.Ok
          (Tests.Legacy__proverif_ping_pong__lib.A.A2.mk
            (received := received))))