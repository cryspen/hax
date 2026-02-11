
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


namespace new_tests.legacy__proverif_ping_pong__lib.a

structure A0 where
  data : u8

structure A1 where
  -- no fields

structure A2 where
  received : u8

def init_a (prologue : (alloc.vec.Vec u8 alloc.alloc.Global)) :
    RustM (core_models.result.Result A0 hax_lib_protocol.ProtocolError) := do
  if
  (← (rust_primitives.hax.machine_int.lt
    (← (alloc.vec.Impl_1.len u8 alloc.alloc.Global prologue))
    (1 : usize))) then
    (pure (core_models.result.Result.Err
      hax_lib_protocol.ProtocolError.InvalidPrologue))
  else
    (pure (core_models.result.Result.Ok
      (A0.mk (data := (← prologue[(0 : usize)]_?)))))

end new_tests.legacy__proverif_ping_pong__lib.a


namespace new_tests.legacy__proverif_ping_pong__lib.b

structure B0 where
  -- no fields

structure B1 where
  received : u8

structure B1alt where
  -- no fields

structure B2 where
  -- no fields

def init_b (_ : rust_primitives.hax.Tuple0) :
    RustM (core_models.result.Result B0 hax_lib_protocol.ProtocolError) := do
  (pure (core_models.result.Result.Ok B0.mk))

end new_tests.legacy__proverif_ping_pong__lib.b


namespace new_tests.legacy__proverif_ping_pong__lib

inductive Message : Type
| Ping : u8 -> Message
| Pong : u8 -> Message

end new_tests.legacy__proverif_ping_pong__lib


namespace new_tests.legacy__proverif_ping_pong__lib.a

def write_ping (state : A0) :
    RustM
    (core_models.result.Result
      (rust_primitives.hax.Tuple2
        A1
        new_tests.legacy__proverif_ping_pong__lib.Message)
      hax_lib_protocol.ProtocolError)
    := do
  (pure (core_models.result.Result.Ok
    (rust_primitives.hax.Tuple2.mk
      A1.mk
      (new_tests.legacy__proverif_ping_pong__lib.Message.Ping
        (A0.data state)))))

def read_pong
    (_state : A1)
    (msg : new_tests.legacy__proverif_ping_pong__lib.Message) :
    RustM (core_models.result.Result A2 hax_lib_protocol.ProtocolError) := do
  match msg with
    | (new_tests.legacy__proverif_ping_pong__lib.Message.Ping  _) =>
      (pure (core_models.result.Result.Err
        hax_lib_protocol.ProtocolError.InvalidMessage))
    | (new_tests.legacy__proverif_ping_pong__lib.Message.Pong  received) =>
      (pure (core_models.result.Result.Ok (A2.mk (received := received))))

end new_tests.legacy__proverif_ping_pong__lib.a


namespace new_tests.legacy__proverif_ping_pong__lib.b

def read_ping
    (_state : B0)
    (msg : new_tests.legacy__proverif_ping_pong__lib.Message) :
    RustM (core_models.result.Result B1 hax_lib_protocol.ProtocolError) := do
  match msg with
    | (new_tests.legacy__proverif_ping_pong__lib.Message.Ping  received) =>
      (pure (core_models.result.Result.Ok (B1.mk (received := received))))
    | (new_tests.legacy__proverif_ping_pong__lib.Message.Pong  _) =>
      (pure (core_models.result.Result.Err
        hax_lib_protocol.ProtocolError.InvalidMessage))

--  @fail(extraction): proverif(HAX0008)
def read_ping_alt
    (_state : B0)
    (msg : new_tests.legacy__proverif_ping_pong__lib.Message) :
    RustM (core_models.result.Result B1alt hax_lib_protocol.ProtocolError) := do
  match
    (← match msg with
      | (new_tests.legacy__proverif_ping_pong__lib.Message.Ping  received) =>
        match (← (rust_primitives.hax.machine_int.eq received (42 : u8))) with
          | true =>
            (pure (core_models.option.Option.Some
              (core_models.result.Result.Ok B1alt.mk)))
          | _ => (pure core_models.option.Option.None)
      | _ => (pure core_models.option.Option.None))
  with
    | (core_models.option.Option.Some  x) => (pure x)
    | (core_models.option.Option.None ) =>
      (pure (core_models.result.Result.Err
        hax_lib_protocol.ProtocolError.InvalidMessage))

def write_pong (state : B1) :
    RustM
    (core_models.result.Result
      (rust_primitives.hax.Tuple2
        B2
        new_tests.legacy__proverif_ping_pong__lib.Message)
      hax_lib_protocol.ProtocolError)
    := do
  (pure (core_models.result.Result.Ok
    (rust_primitives.hax.Tuple2.mk
      B2.mk
      (new_tests.legacy__proverif_ping_pong__lib.Message.Pong
        (B1.received state)))))

end new_tests.legacy__proverif_ping_pong__lib.b

