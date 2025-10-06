module Tests.Legacy__proverif_noise__lib.Noise_crypto
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Hax_lib_protocol.Crypto in
  ()

/// This file formalizes the Crypto Functions from the Noise Specification
/// Section 4: Crypto Functions
/// https://noiseprotocol.org/noise.html#crypto-functions
type t_Error = | Error_CryptoError : t_Error

let t_Error_cast_to_repr (x: t_Error) : isize =
  match x <: t_Error with | Error_CryptoError  -> mk_isize 0

/// Section 4.1 and 12.1: Diffie-Hellman Functions for Curve25519
type t_KeyPair = {
  f_private_key:Hax_lib_protocol.Crypto.t_DHScalar;
  f_public_key:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global
}

let v_DHLEN: usize = mk_usize 32

let generate_keypair (sk: t_Slice u8) : t_KeyPair =
  let sk:Hax_lib_protocol.Crypto.t_DHScalar =
    Hax_lib_protocol.Crypto.impl_DHScalar__from_bytes sk
  in
  let pk:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Hax_lib_protocol.Crypto.dh_scalar_multiply_base (Hax_lib_protocol.Crypto.DHGroup_X25519
        <:
        Hax_lib_protocol.Crypto.t_DHGroup)
      (Core.Clone.f_clone #Hax_lib_protocol.Crypto.t_DHScalar #FStar.Tactics.Typeclasses.solve sk
        <:
        Hax_lib_protocol.Crypto.t_DHScalar)
  in
  { f_private_key = sk; f_public_key = pk } <: t_KeyPair

let dh (sk: t_KeyPair) (pk: t_Slice u8) : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  let pk:Hax_lib_protocol.Crypto.t_DHElement =
    Hax_lib_protocol.Crypto.impl_DHElement__from_bytes pk
  in
  Hax_lib_protocol.Crypto.dh_scalar_multiply (Hax_lib_protocol.Crypto.DHGroup_X25519
      <:
      Hax_lib_protocol.Crypto.t_DHGroup)
    (Core.Clone.f_clone #Hax_lib_protocol.Crypto.t_DHScalar
        #FStar.Tactics.Typeclasses.solve
        sk.f_private_key
      <:
      Hax_lib_protocol.Crypto.t_DHScalar)
    pk

/// Section 4.2 and 12.3: Cipher functions for ChaCha20-Poly1305
let encrypt (key: t_Slice u8) (counter: u64) (aad plain: t_Slice u8)
    : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  let chacha_iv:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Alloc.Vec.from_elem #u8 (mk_u8 0) (mk_usize 4)
  in
  let chacha_iv:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Alloc.Vec.impl_2__extend_from_slice #u8
      #Alloc.Alloc.t_Global
      chacha_iv
      (Core.Num.impl_u64__to_le_bytes counter <: t_Slice u8)
  in
  let cipher, tag:(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global
  ) =
    Hax_lib_protocol.Crypto.aead_encrypt (Hax_lib_protocol.Crypto.impl_AEADKey__from_bytes (Hax_lib_protocol.Crypto.AEADAlgorithm_Chacha20Poly1305
            <:
            Hax_lib_protocol.Crypto.t_AEADAlgorithm)
          key
        <:
        Hax_lib_protocol.Crypto.t_AEADKey)
      (Hax_lib_protocol.Crypto.impl_AEADIV__from_bytes (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8
                  Alloc.Alloc.t_Global)
              #FStar.Tactics.Typeclasses.solve
              chacha_iv
            <:
            t_Slice u8)
        <:
        Hax_lib_protocol.Crypto.t_AEADIV)
      aad
      plain
  in
  let cipher:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Alloc.Vec.impl_2__extend_from_slice #u8
      #Alloc.Alloc.t_Global
      cipher
      (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          tag
        <:
        t_Slice u8)
  in
  cipher

let decrypt (key: t_Slice u8) (counter: u64) (aad cipher: t_Slice u8)
    : Core.Result.t_Result (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) t_Error =
  let chacha_iv:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Alloc.Vec.from_elem #u8 (mk_u8 0) (mk_usize 4)
  in
  let chacha_iv:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Alloc.Vec.impl_2__extend_from_slice #u8
      #Alloc.Alloc.t_Global
      chacha_iv
      (Core.Num.impl_u64__to_le_bytes counter <: t_Slice u8)
  in
  let cipher_len:usize = (Core.Slice.impl__len #u8 cipher <: usize) -! mk_usize 16 in
  let cip:t_Slice u8 =
    cipher.[ { Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = cipher_len }
      <:
      Core.Ops.Range.t_Range usize ]
  in
  let tag:t_Slice u8 =
    cipher.[ {
        Core.Ops.Range.f_start = cipher_len;
        Core.Ops.Range.f_end = Core.Slice.impl__len #u8 cipher <: usize
      }
      <:
      Core.Ops.Range.t_Range usize ]
  in
  Core.Result.impl__map_err #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
    #Hax_lib_protocol.t_ProtocolError
    #t_Error
    (Hax_lib_protocol.Crypto.aead_decrypt (Hax_lib_protocol.Crypto.impl_AEADKey__from_bytes (Hax_lib_protocol.Crypto.AEADAlgorithm_Chacha20Poly1305
              <:
              Hax_lib_protocol.Crypto.t_AEADAlgorithm)
            key
          <:
          Hax_lib_protocol.Crypto.t_AEADKey)
        (Hax_lib_protocol.Crypto.impl_AEADIV__from_bytes (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec
                    u8 Alloc.Alloc.t_Global)
                #FStar.Tactics.Typeclasses.solve
                chacha_iv
              <:
              t_Slice u8)
          <:
          Hax_lib_protocol.Crypto.t_AEADIV)
        aad
        cip
        (Hax_lib_protocol.Crypto.impl_AEADTag__from_bytes tag <: Hax_lib_protocol.Crypto.t_AEADTag)
      <:
      Core.Result.t_Result (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
        Hax_lib_protocol.t_ProtocolError)
    (fun temp_0_ ->
        let _:Hax_lib_protocol.t_ProtocolError = temp_0_ in
        Error_CryptoError <: t_Error)

let rekey (key: t_Slice u8) : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  encrypt key
    (mk_u64 18446744073709551615)
    (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
        #FStar.Tactics.Typeclasses.solve
        (Alloc.Vec.impl__new #u8 () <: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      <:
      t_Slice u8)
    (Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) <: t_Slice u8)

/// Section 4.3 and 12.5: Hash functions for SHA-256
let v_HASHLEN: usize = mk_usize 32

let v_BLOCKLEN: usize = mk_usize 64

let hash (input: t_Slice u8) : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  Hax_lib_protocol.Crypto.hash (Hax_lib_protocol.Crypto.HashAlgorithm_Sha256
      <:
      Hax_lib_protocol.Crypto.t_HashAlgorithm)
    input

let hmac_hash (key input: t_Slice u8) : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  Hax_lib_protocol.Crypto.hmac (Hax_lib_protocol.Crypto.HMACAlgorithm_Sha256
      <:
      Hax_lib_protocol.Crypto.t_HMACAlgorithm)
    key
    input

/// HKDF spec as per Noise
/// Alternative would be to directly use HKDF
let kdf_next (secret prev: t_Slice u8) (counter: u8) : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  hmac_hash secret
    (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
        #FStar.Tactics.Typeclasses.solve
        (Alloc.Slice.impl__concat #(t_Slice u8)
            #u8
            ((let list =
                  [
                    prev;
                    (let list = [counter] in
                      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                      Rust_primitives.Hax.array_of_list 1 list)
                    <:
                    t_Slice u8
                  ]
                in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                Rust_primitives.Hax.array_of_list 2 list)
              <:
              t_Slice (t_Slice u8))
          <:
          Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      <:
      t_Slice u8)

let hkdf1 (key ikm: t_Slice u8) : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  let secret:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = hmac_hash key ikm in
  kdf_next (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
        #FStar.Tactics.Typeclasses.solve
        secret
      <:
      t_Slice u8)
    (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
        #FStar.Tactics.Typeclasses.solve
        (Alloc.Vec.impl__new #u8 () <: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      <:
      t_Slice u8)
    (mk_u8 1)

let hkdf2 (key ikm: t_Slice u8)
    : (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) =
  let secret:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = hmac_hash key ikm in
  let k1:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    kdf_next (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          secret
        <:
        t_Slice u8)
      (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          (Alloc.Vec.impl__new #u8 () <: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
        <:
        t_Slice u8)
      (mk_u8 1)
  in
  let k2:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    kdf_next (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          secret
        <:
        t_Slice u8)
      (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          k1
        <:
        t_Slice u8)
      (mk_u8 2)
  in
  k1, k2 <: (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)

let hkdf3 (key ikm: t_Slice u8)
    : (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global &
      Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) =
  let secret:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = hmac_hash key ikm in
  let k1:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    kdf_next (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          secret
        <:
        t_Slice u8)
      (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          (Alloc.Vec.impl__new #u8 () <: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
        <:
        t_Slice u8)
      (mk_u8 1)
  in
  let k2:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    kdf_next (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          secret
        <:
        t_Slice u8)
      (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          k1
        <:
        t_Slice u8)
      (mk_u8 2)
  in
  let k3:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    kdf_next (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          secret
        <:
        t_Slice u8)
      (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          k1
        <:
        t_Slice u8)
      (mk_u8 3)
  in
  k1, k2, k3
  <:
  (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global &
    Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
