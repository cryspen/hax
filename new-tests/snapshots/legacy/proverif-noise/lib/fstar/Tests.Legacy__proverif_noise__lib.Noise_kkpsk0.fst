module Tests.Legacy__proverif_noise__lib.Noise_kkpsk0
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_HandshakeStateI0 = {
  f_st:Tests.Legacy__proverif_noise__lib.Noise_lib.t_SymmetricState;
  f_psk:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global;
  f_s:Tests.Legacy__proverif_noise__lib.Noise_crypto.t_KeyPair;
  f_e:Tests.Legacy__proverif_noise__lib.Noise_crypto.t_KeyPair;
  f_rs:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global
}

type t_HandshakeStateI1 = {
  f_st:Tests.Legacy__proverif_noise__lib.Noise_lib.t_SymmetricState;
  f_s:Tests.Legacy__proverif_noise__lib.Noise_crypto.t_KeyPair;
  f_e:Tests.Legacy__proverif_noise__lib.Noise_crypto.t_KeyPair
}

type t_HandshakeStateR0 = {
  f_st:Tests.Legacy__proverif_noise__lib.Noise_lib.t_SymmetricState;
  f_psk:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global;
  f_s:Tests.Legacy__proverif_noise__lib.Noise_crypto.t_KeyPair;
  f_e:Tests.Legacy__proverif_noise__lib.Noise_crypto.t_KeyPair;
  f_rs:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global
}

type t_HandshakeStateR1 = {
  f_st:Tests.Legacy__proverif_noise__lib.Noise_lib.t_SymmetricState;
  f_e:Tests.Legacy__proverif_noise__lib.Noise_crypto.t_KeyPair;
  f_rs:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global;
  f_re:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global
}

type t_Transport = {
  f_send:Tests.Legacy__proverif_noise__lib.Noise_lib.t_CipherState;
  f_recv:Tests.Legacy__proverif_noise__lib.Noise_lib.t_CipherState;
  f_handshake_hash:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global
}

type t_ProtocolName = | ProtocolName : t_Array u8 (mk_usize 36) -> t_ProtocolName

let v_Noise_KKpsk0_25519_ChaChaPoly_SHA256: t_ProtocolName =
  ProtocolName
  (let list =
      [
        mk_u8 78; mk_u8 111; mk_u8 105; mk_u8 115; mk_u8 101; mk_u8 95; mk_u8 75; mk_u8 75;
        mk_u8 112; mk_u8 115; mk_u8 107; mk_u8 48; mk_u8 95; mk_u8 50; mk_u8 53; mk_u8 53; mk_u8 49;
        mk_u8 57; mk_u8 95; mk_u8 67; mk_u8 104; mk_u8 97; mk_u8 67; mk_u8 104; mk_u8 97; mk_u8 80;
        mk_u8 111; mk_u8 108; mk_u8 121; mk_u8 95; mk_u8 83; mk_u8 72; mk_u8 65; mk_u8 50; mk_u8 53;
        mk_u8 54
      ]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 36);
    Rust_primitives.Hax.array_of_list 36 list)
  <:
  t_ProtocolName

///  KKpsk0:
///    -> s
///    <- s
///    ...
let initialize_initiator
      (prologue: t_Slice u8)
      (psk: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      (s e: Tests.Legacy__proverif_noise__lib.Noise_crypto.t_KeyPair)
      (rs: t_Slice u8)
    : t_HandshakeStateI0 =
  let st:Tests.Legacy__proverif_noise__lib.Noise_lib.t_SymmetricState =
    Tests.Legacy__proverif_noise__lib.Noise_lib.initialize_symmetric (v_Noise_KKpsk0_25519_ChaChaPoly_SHA256
          ._0
        <:
        t_Slice u8)
  in
  let st:Tests.Legacy__proverif_noise__lib.Noise_lib.t_SymmetricState =
    Tests.Legacy__proverif_noise__lib.Noise_lib.mix_hash st prologue
  in
  let st:Tests.Legacy__proverif_noise__lib.Noise_lib.t_SymmetricState =
    Tests.Legacy__proverif_noise__lib.Noise_lib.mix_hash st
      (Core_models.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          s.Tests.Legacy__proverif_noise__lib.Noise_crypto.f_public_key
        <:
        t_Slice u8)
  in
  let st:Tests.Legacy__proverif_noise__lib.Noise_lib.t_SymmetricState =
    Tests.Legacy__proverif_noise__lib.Noise_lib.mix_hash st rs
  in
  { f_psk = psk; f_st = st; f_s = s; f_e = e; f_rs = Alloc.Slice.impl__to_vec #u8 rs }
  <:
  t_HandshakeStateI0

let initialize_responder
      (prologue: t_Slice u8)
      (psk: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      (s e: Tests.Legacy__proverif_noise__lib.Noise_crypto.t_KeyPair)
      (rs: t_Slice u8)
    : t_HandshakeStateR0 =
  let st:Tests.Legacy__proverif_noise__lib.Noise_lib.t_SymmetricState =
    Tests.Legacy__proverif_noise__lib.Noise_lib.initialize_symmetric (v_Noise_KKpsk0_25519_ChaChaPoly_SHA256
          ._0
        <:
        t_Slice u8)
  in
  let st:Tests.Legacy__proverif_noise__lib.Noise_lib.t_SymmetricState =
    Tests.Legacy__proverif_noise__lib.Noise_lib.mix_hash st prologue
  in
  let st:Tests.Legacy__proverif_noise__lib.Noise_lib.t_SymmetricState =
    Tests.Legacy__proverif_noise__lib.Noise_lib.mix_hash st rs
  in
  let st:Tests.Legacy__proverif_noise__lib.Noise_lib.t_SymmetricState =
    Tests.Legacy__proverif_noise__lib.Noise_lib.mix_hash st
      (Core_models.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          s.Tests.Legacy__proverif_noise__lib.Noise_crypto.f_public_key
        <:
        t_Slice u8)
  in
  { f_st = st; f_psk = psk; f_s = s; f_e = e; f_rs = Alloc.Slice.impl__to_vec #u8 rs }
  <:
  t_HandshakeStateR0

///  KKpsk0:
///    ...
///    -> psk, e, es, ss
/// @fail(extraction): ssprove(HAX0001)
let write_message1 (hs: t_HandshakeStateI0) (payload: t_Slice u8)
    : Core_models.Result.t_Result (t_HandshakeStateI1 & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error =
  let { f_st = st ; f_psk = psk ; f_s = s ; f_e = e ; f_rs = rs }:t_HandshakeStateI0 = hs in
  let st:Tests.Legacy__proverif_noise__lib.Noise_lib.t_SymmetricState =
    Tests.Legacy__proverif_noise__lib.Noise_lib.mix_key_and_hash st
      (Core_models.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          psk
        <:
        t_Slice u8)
  in
  let st:Tests.Legacy__proverif_noise__lib.Noise_lib.t_SymmetricState =
    Tests.Legacy__proverif_noise__lib.Noise_lib.mix_hash st
      (Core_models.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          e.Tests.Legacy__proverif_noise__lib.Noise_crypto.f_public_key
        <:
        t_Slice u8)
  in
  let st:Tests.Legacy__proverif_noise__lib.Noise_lib.t_SymmetricState =
    Tests.Legacy__proverif_noise__lib.Noise_lib.mix_key st
      (Core_models.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          e.Tests.Legacy__proverif_noise__lib.Noise_crypto.f_public_key
        <:
        t_Slice u8)
  in
  let es:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Tests.Legacy__proverif_noise__lib.Noise_crypto.dh e
      (Core_models.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          rs
        <:
        t_Slice u8)
  in
  let st:Tests.Legacy__proverif_noise__lib.Noise_lib.t_SymmetricState =
    Tests.Legacy__proverif_noise__lib.Noise_lib.mix_key st
      (Core_models.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          es
        <:
        t_Slice u8)
  in
  let ss:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Tests.Legacy__proverif_noise__lib.Noise_crypto.dh s
      (Core_models.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          rs
        <:
        t_Slice u8)
  in
  let st:Tests.Legacy__proverif_noise__lib.Noise_lib.t_SymmetricState =
    Tests.Legacy__proverif_noise__lib.Noise_lib.mix_key st
      (Core_models.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          ss
        <:
        t_Slice u8)
  in
  match
    Tests.Legacy__proverif_noise__lib.Noise_lib.encrypt_and_hash st payload
    <:
    Core_models.Result.t_Result
      (Tests.Legacy__proverif_noise__lib.Noise_lib.t_SymmetricState &
        Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error
  with
  | Core_models.Result.Result_Ok (st, ciphertext) ->
    let hs:t_HandshakeStateI1 = { f_st = st; f_s = s; f_e = e } <: t_HandshakeStateI1 in
    Core_models.Result.Result_Ok
    (hs, ciphertext <: (t_HandshakeStateI1 & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
    <:
    Core_models.Result.t_Result (t_HandshakeStateI1 & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error
  | Core_models.Result.Result_Err err ->
    Core_models.Result.Result_Err err
    <:
    Core_models.Result.t_Result (t_HandshakeStateI1 & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error

/// @fail(extraction): ssprove(HAX0001)
let read_message1 (hs: t_HandshakeStateR0) (ciphertext: t_Slice u8)
    : Core_models.Result.t_Result (t_HandshakeStateR1 & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error =
  let { f_st = st ; f_psk = psk ; f_s = s ; f_e = e ; f_rs = rs }:t_HandshakeStateR0 = hs in
  let re:t_Slice u8 =
    ciphertext.[ {
        Core_models.Ops.Range.f_start = mk_usize 0;
        Core_models.Ops.Range.f_end = Tests.Legacy__proverif_noise__lib.Noise_crypto.v_DHLEN
      }
      <:
      Core_models.Ops.Range.t_Range usize ]
  in
  let ciphertext:t_Slice u8 =
    ciphertext.[ {
        Core_models.Ops.Range.f_start = Tests.Legacy__proverif_noise__lib.Noise_crypto.v_DHLEN;
        Core_models.Ops.Range.f_end = Core_models.Slice.impl__len #u8 ciphertext <: usize
      }
      <:
      Core_models.Ops.Range.t_Range usize ]
  in
  let st:Tests.Legacy__proverif_noise__lib.Noise_lib.t_SymmetricState =
    Tests.Legacy__proverif_noise__lib.Noise_lib.mix_key_and_hash st
      (Core_models.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          psk
        <:
        t_Slice u8)
  in
  let st:Tests.Legacy__proverif_noise__lib.Noise_lib.t_SymmetricState =
    Tests.Legacy__proverif_noise__lib.Noise_lib.mix_hash st re
  in
  let st:Tests.Legacy__proverif_noise__lib.Noise_lib.t_SymmetricState =
    Tests.Legacy__proverif_noise__lib.Noise_lib.mix_key st re
  in
  let es:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Tests.Legacy__proverif_noise__lib.Noise_crypto.dh s re
  in
  let st:Tests.Legacy__proverif_noise__lib.Noise_lib.t_SymmetricState =
    Tests.Legacy__proverif_noise__lib.Noise_lib.mix_key st
      (Core_models.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          es
        <:
        t_Slice u8)
  in
  let ss:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Tests.Legacy__proverif_noise__lib.Noise_crypto.dh s
      (Core_models.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          rs
        <:
        t_Slice u8)
  in
  let st:Tests.Legacy__proverif_noise__lib.Noise_lib.t_SymmetricState =
    Tests.Legacy__proverif_noise__lib.Noise_lib.mix_key st
      (Core_models.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          ss
        <:
        t_Slice u8)
  in
  match
    Tests.Legacy__proverif_noise__lib.Noise_lib.decrypt_and_hash st ciphertext
    <:
    Core_models.Result.t_Result
      (Tests.Legacy__proverif_noise__lib.Noise_lib.t_SymmetricState &
        Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error
  with
  | Core_models.Result.Result_Ok (st, plaintext) ->
    let hs:t_HandshakeStateR1 =
      { f_st = st; f_e = e; f_rs = rs; f_re = Alloc.Slice.impl__to_vec #u8 re }
      <:
      t_HandshakeStateR1
    in
    Core_models.Result.Result_Ok
    (hs, plaintext <: (t_HandshakeStateR1 & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
    <:
    Core_models.Result.t_Result (t_HandshakeStateR1 & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error
  | Core_models.Result.Result_Err err ->
    Core_models.Result.Result_Err err
    <:
    Core_models.Result.t_Result (t_HandshakeStateR1 & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error

///  KKpsk0:
///    ...
///     <- e, ee, se
/// @fail(extraction): ssprove(HAX0001)
let write_message2 (hs: t_HandshakeStateR1) (payload: t_Slice u8)
    : Core_models.Result.t_Result (t_Transport & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error =
  let { f_st = st ; f_e = e ; f_rs = rs ; f_re = re }:t_HandshakeStateR1 = hs in
  let st:Tests.Legacy__proverif_noise__lib.Noise_lib.t_SymmetricState =
    Tests.Legacy__proverif_noise__lib.Noise_lib.mix_hash st
      (Core_models.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          e.Tests.Legacy__proverif_noise__lib.Noise_crypto.f_public_key
        <:
        t_Slice u8)
  in
  let st:Tests.Legacy__proverif_noise__lib.Noise_lib.t_SymmetricState =
    Tests.Legacy__proverif_noise__lib.Noise_lib.mix_key st
      (Core_models.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          e.Tests.Legacy__proverif_noise__lib.Noise_crypto.f_public_key
        <:
        t_Slice u8)
  in
  let ee:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Tests.Legacy__proverif_noise__lib.Noise_crypto.dh e
      (Core_models.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          re
        <:
        t_Slice u8)
  in
  let st:Tests.Legacy__proverif_noise__lib.Noise_lib.t_SymmetricState =
    Tests.Legacy__proverif_noise__lib.Noise_lib.mix_key st
      (Core_models.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          ee
        <:
        t_Slice u8)
  in
  let se:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Tests.Legacy__proverif_noise__lib.Noise_crypto.dh e
      (Core_models.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          rs
        <:
        t_Slice u8)
  in
  let st:Tests.Legacy__proverif_noise__lib.Noise_lib.t_SymmetricState =
    Tests.Legacy__proverif_noise__lib.Noise_lib.mix_key st
      (Core_models.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          se
        <:
        t_Slice u8)
  in
  match
    Tests.Legacy__proverif_noise__lib.Noise_lib.encrypt_and_hash st payload
    <:
    Core_models.Result.t_Result
      (Tests.Legacy__proverif_noise__lib.Noise_lib.t_SymmetricState &
        Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error
  with
  | Core_models.Result.Result_Ok (st, ciphertext) ->
    let
    (c1: Tests.Legacy__proverif_noise__lib.Noise_lib.t_CipherState),
    (c2: Tests.Legacy__proverif_noise__lib.Noise_lib.t_CipherState),
    (h: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) =
      Tests.Legacy__proverif_noise__lib.Noise_lib.split st
    in
    let tx:t_Transport = { f_send = c2; f_recv = c1; f_handshake_hash = h } <: t_Transport in
    Core_models.Result.Result_Ok
    (tx, ciphertext <: (t_Transport & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
    <:
    Core_models.Result.t_Result (t_Transport & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error
  | Core_models.Result.Result_Err err ->
    Core_models.Result.Result_Err err
    <:
    Core_models.Result.t_Result (t_Transport & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error

/// @fail(extraction): ssprove(HAX0001)
let read_message2 (hs: t_HandshakeStateI1) (ciphertext: t_Slice u8)
    : Core_models.Result.t_Result (t_Transport & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error =
  let { f_st = st ; f_s = s ; f_e = e }:t_HandshakeStateI1 = hs in
  let re:t_Slice u8 =
    ciphertext.[ {
        Core_models.Ops.Range.f_start = mk_usize 0;
        Core_models.Ops.Range.f_end = Tests.Legacy__proverif_noise__lib.Noise_crypto.v_DHLEN
      }
      <:
      Core_models.Ops.Range.t_Range usize ]
  in
  let ciphertext:t_Slice u8 =
    ciphertext.[ {
        Core_models.Ops.Range.f_start = Tests.Legacy__proverif_noise__lib.Noise_crypto.v_DHLEN;
        Core_models.Ops.Range.f_end = Core_models.Slice.impl__len #u8 ciphertext <: usize
      }
      <:
      Core_models.Ops.Range.t_Range usize ]
  in
  let st:Tests.Legacy__proverif_noise__lib.Noise_lib.t_SymmetricState =
    Tests.Legacy__proverif_noise__lib.Noise_lib.mix_hash st re
  in
  let st:Tests.Legacy__proverif_noise__lib.Noise_lib.t_SymmetricState =
    Tests.Legacy__proverif_noise__lib.Noise_lib.mix_key st re
  in
  let ee:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Tests.Legacy__proverif_noise__lib.Noise_crypto.dh e re
  in
  let st:Tests.Legacy__proverif_noise__lib.Noise_lib.t_SymmetricState =
    Tests.Legacy__proverif_noise__lib.Noise_lib.mix_key st
      (Core_models.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          ee
        <:
        t_Slice u8)
  in
  let se:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Tests.Legacy__proverif_noise__lib.Noise_crypto.dh s re
  in
  let st:Tests.Legacy__proverif_noise__lib.Noise_lib.t_SymmetricState =
    Tests.Legacy__proverif_noise__lib.Noise_lib.mix_key st
      (Core_models.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          se
        <:
        t_Slice u8)
  in
  match
    Tests.Legacy__proverif_noise__lib.Noise_lib.decrypt_and_hash st ciphertext
    <:
    Core_models.Result.t_Result
      (Tests.Legacy__proverif_noise__lib.Noise_lib.t_SymmetricState &
        Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error
  with
  | Core_models.Result.Result_Ok (st, plaintext) ->
    let
    (c1: Tests.Legacy__proverif_noise__lib.Noise_lib.t_CipherState),
    (c2: Tests.Legacy__proverif_noise__lib.Noise_lib.t_CipherState),
    (h: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) =
      Tests.Legacy__proverif_noise__lib.Noise_lib.split st
    in
    let tx:t_Transport = { f_send = c1; f_recv = c2; f_handshake_hash = h } <: t_Transport in
    Core_models.Result.Result_Ok
    (tx, plaintext <: (t_Transport & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
    <:
    Core_models.Result.t_Result (t_Transport & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error
  | Core_models.Result.Result_Err err ->
    Core_models.Result.Result_Err err
    <:
    Core_models.Result.t_Result (t_Transport & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error

///  KKpsk0:
///    ->
///    <-
/// @fail(extraction): ssprove(HAX0001)
let write_transport (tx: t_Transport) (ad payload: t_Slice u8)
    : Core_models.Result.t_Result (t_Transport & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error =
  let { f_send = send ; f_recv = recv ; f_handshake_hash = handshake_hash }:t_Transport = tx in
  match
    Tests.Legacy__proverif_noise__lib.Noise_lib.encrypt_with_ad send ad payload
    <:
    Core_models.Result.t_Result
      (Tests.Legacy__proverif_noise__lib.Noise_lib.t_CipherState &
        Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error
  with
  | Core_models.Result.Result_Ok (send, ciphertext) ->
    let tx:t_Transport =
      { f_send = send; f_recv = recv; f_handshake_hash = handshake_hash } <: t_Transport
    in
    Core_models.Result.Result_Ok
    (tx, ciphertext <: (t_Transport & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
    <:
    Core_models.Result.t_Result (t_Transport & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error
  | Core_models.Result.Result_Err err ->
    Core_models.Result.Result_Err err
    <:
    Core_models.Result.t_Result (t_Transport & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error

/// @fail(extraction): ssprove(HAX0001)
let read_transport (tx: t_Transport) (ad ciphertext: t_Slice u8)
    : Core_models.Result.t_Result (t_Transport & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error =
  let { f_send = send ; f_recv = recv ; f_handshake_hash = handshake_hash }:t_Transport = tx in
  match
    Tests.Legacy__proverif_noise__lib.Noise_lib.decrypt_with_ad recv ad ciphertext
    <:
    Core_models.Result.t_Result
      (Tests.Legacy__proverif_noise__lib.Noise_lib.t_CipherState &
        Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error
  with
  | Core_models.Result.Result_Ok (recv, payload) ->
    let tx:t_Transport =
      { f_send = send; f_recv = recv; f_handshake_hash = handshake_hash } <: t_Transport
    in
    Core_models.Result.Result_Ok
    (tx, payload <: (t_Transport & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
    <:
    Core_models.Result.t_Result (t_Transport & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error
  | Core_models.Result.Result_Err err ->
    Core_models.Result.Result_Err err
    <:
    Core_models.Result.t_Result (t_Transport & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error
