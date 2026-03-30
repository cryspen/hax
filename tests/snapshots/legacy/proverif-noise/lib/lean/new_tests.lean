
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


namespace new_tests.legacy__proverif_noise__lib.noise_crypto

--  This file formalizes the Crypto Functions from the Noise Specification
--  Section 4: Crypto Functions
--  https://noiseprotocol.org/noise.html#crypto-functions
inductive Error : Type
| CryptoError : Error

@[spec]
def Error_cast_to_repr (x : Error) : RustM isize := do
  match x with | (Error.CryptoError ) => do (pure (0 : isize))

--  Section 4.1 and 12.1: Diffie-Hellman Functions for Curve25519
structure KeyPair where
  private_key : hax_lib_protocol.crypto.DHScalar
  public_key : (alloc.vec.Vec u8 alloc.alloc.Global)

def DHLEN : usize := (32 : usize)

@[spec]
def generate_keypair (sk : (RustSlice u8)) : RustM KeyPair := do
  let sk : hax_lib_protocol.crypto.DHScalar ←
    (hax_lib_protocol.crypto.Impl.from_bytes sk);
  let pk : (alloc.vec.Vec u8 alloc.alloc.Global) ←
    (hax_lib_protocol.crypto.dh_scalar_multiply_base
      hax_lib_protocol.crypto.DHGroup.X25519
      (← (core_models.clone.Clone.clone hax_lib_protocol.crypto.DHScalar sk)));
  (pure (KeyPair.mk (private_key := sk) (public_key := pk)))

@[spec]
def dh (sk : KeyPair) (pk : (RustSlice u8)) :
    RustM (alloc.vec.Vec u8 alloc.alloc.Global) := do
  let pk : hax_lib_protocol.crypto.DHElement ←
    (hax_lib_protocol.crypto.Impl_1.from_bytes pk);
  (hax_lib_protocol.crypto.dh_scalar_multiply
    hax_lib_protocol.crypto.DHGroup.X25519
    (← (core_models.clone.Clone.clone
      hax_lib_protocol.crypto.DHScalar (KeyPair.private_key sk)))
    pk)

--  Section 4.2 and 12.3: Cipher functions for ChaCha20-Poly1305
@[spec]
def encrypt
    (key : (RustSlice u8))
    (counter : u64)
    (aad : (RustSlice u8))
    (plain : (RustSlice u8)) :
    RustM (alloc.vec.Vec u8 alloc.alloc.Global) := do
  let chacha_iv : (alloc.vec.Vec u8 alloc.alloc.Global) ←
    (alloc.vec.from_elem u8 (0 : u8) (4 : usize));
  let chacha_iv : (alloc.vec.Vec u8 alloc.alloc.Global) ←
    (alloc.vec.Impl_2.extend_from_slice u8 alloc.alloc.Global
      chacha_iv
      (← (rust_primitives.unsize
        (← (core_models.num.Impl_9.to_le_bytes counter)))));
  let ⟨cipher, tag⟩ ←
    (hax_lib_protocol.crypto.aead_encrypt
      (← (hax_lib_protocol.crypto.Impl_4.from_bytes
        hax_lib_protocol.crypto.AEADAlgorithm.Chacha20Poly1305
        key))
      (← (hax_lib_protocol.crypto.Impl_5.from_bytes
        (← (core_models.ops.deref.Deref.deref
          (alloc.vec.Vec u8 alloc.alloc.Global) chacha_iv))))
      aad
      plain);
  let cipher : (alloc.vec.Vec u8 alloc.alloc.Global) ←
    (alloc.vec.Impl_2.extend_from_slice u8 alloc.alloc.Global
      cipher
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global) tag)));
  (pure cipher)

@[spec]
def decrypt
    (key : (RustSlice u8))
    (counter : u64)
    (aad : (RustSlice u8))
    (cipher : (RustSlice u8)) :
    RustM
    (core_models.result.Result (alloc.vec.Vec u8 alloc.alloc.Global) Error)
    := do
  let chacha_iv : (alloc.vec.Vec u8 alloc.alloc.Global) ←
    (alloc.vec.from_elem u8 (0 : u8) (4 : usize));
  let chacha_iv : (alloc.vec.Vec u8 alloc.alloc.Global) ←
    (alloc.vec.Impl_2.extend_from_slice u8 alloc.alloc.Global
      chacha_iv
      (← (rust_primitives.unsize
        (← (core_models.num.Impl_9.to_le_bytes counter)))));
  let cipher_len : usize ←
    ((← (core_models.slice.Impl.len u8 cipher)) -? (16 : usize));
  let cip : (RustSlice u8) ←
    cipher[
      (core_models.ops.range.Range.mk
        (start := (0 : usize))
        (_end := cipher_len))
      ]_?;
  let tag : (RustSlice u8) ←
    cipher[
      (core_models.ops.range.Range.mk
        (start := cipher_len)
        (_end := (← (core_models.slice.Impl.len u8 cipher))))
      ]_?;
  (core_models.result.Impl.map_err
    (alloc.vec.Vec u8 alloc.alloc.Global)
    hax_lib_protocol.ProtocolError
    Error
    (hax_lib_protocol.ProtocolError -> RustM Error)
    (← (hax_lib_protocol.crypto.aead_decrypt
      (← (hax_lib_protocol.crypto.Impl_4.from_bytes
        hax_lib_protocol.crypto.AEADAlgorithm.Chacha20Poly1305
        key))
      (← (hax_lib_protocol.crypto.Impl_5.from_bytes
        (← (core_models.ops.deref.Deref.deref
          (alloc.vec.Vec u8 alloc.alloc.Global) chacha_iv))))
      aad
      cip
      (← (hax_lib_protocol.crypto.Impl_6.from_bytes tag))))
    (fun _ => (do (pure Error.CryptoError) : RustM Error)))

@[spec]
def rekey (key : (RustSlice u8)) :
    RustM (alloc.vec.Vec u8 alloc.alloc.Global) := do
  (encrypt
    key
    (18446744073709551615 : u64)
    (← (core_models.ops.deref.Deref.deref
      (alloc.vec.Vec u8 alloc.alloc.Global)
      (← (alloc.vec.Impl.new u8 rust_primitives.hax.Tuple0.mk))))
    (← (rust_primitives.unsize
      (← (rust_primitives.hax.repeat (0 : u8) (32 : usize))))))

--  Section 4.3 and 12.5: Hash functions for SHA-256
def HASHLEN : usize := (32 : usize)

def BLOCKLEN : usize := (64 : usize)

@[spec]
def hash (input : (RustSlice u8)) :
    RustM (alloc.vec.Vec u8 alloc.alloc.Global) := do
  (hax_lib_protocol.crypto.hash
    hax_lib_protocol.crypto.HashAlgorithm.Sha256
    input)

@[spec]
def hmac_hash (key : (RustSlice u8)) (input : (RustSlice u8)) :
    RustM (alloc.vec.Vec u8 alloc.alloc.Global) := do
  (hax_lib_protocol.crypto.hmac
    hax_lib_protocol.crypto.HMACAlgorithm.Sha256
    key
    input)

--  HKDF spec as per Noise
--  Alternative would be to directly use HKDF
@[spec]
def kdf_next (secret : (RustSlice u8)) (prev : (RustSlice u8)) (counter : u8) :
    RustM (alloc.vec.Vec u8 alloc.alloc.Global) := do
  (hmac_hash
    secret
    (← (core_models.ops.deref.Deref.deref
      (alloc.vec.Vec u8 alloc.alloc.Global)
      (← (alloc.slice.Impl.concat (RustSlice u8) u8
        (← (rust_primitives.unsize
          (RustArray.ofVec #v[prev,
                                (← (rust_primitives.unsize
                                  (RustArray.ofVec #v[counter])))]))))))))

@[spec]
def hkdf1 (key : (RustSlice u8)) (ikm : (RustSlice u8)) :
    RustM (alloc.vec.Vec u8 alloc.alloc.Global) := do
  let secret : (alloc.vec.Vec u8 alloc.alloc.Global) ← (hmac_hash key ikm);
  (kdf_next
    (← (core_models.ops.deref.Deref.deref
      (alloc.vec.Vec u8 alloc.alloc.Global) secret))
    (← (core_models.ops.deref.Deref.deref
      (alloc.vec.Vec u8 alloc.alloc.Global)
      (← (alloc.vec.Impl.new u8 rust_primitives.hax.Tuple0.mk))))
    (1 : u8))

@[spec]
def hkdf2 (key : (RustSlice u8)) (ikm : (RustSlice u8)) :
    RustM
    (rust_primitives.hax.Tuple2
      (alloc.vec.Vec u8 alloc.alloc.Global)
      (alloc.vec.Vec u8 alloc.alloc.Global))
    := do
  let secret : (alloc.vec.Vec u8 alloc.alloc.Global) ← (hmac_hash key ikm);
  let k1 : (alloc.vec.Vec u8 alloc.alloc.Global) ←
    (kdf_next
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global) secret))
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global)
        (← (alloc.vec.Impl.new u8 rust_primitives.hax.Tuple0.mk))))
      (1 : u8));
  let k2 : (alloc.vec.Vec u8 alloc.alloc.Global) ←
    (kdf_next
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global) secret))
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global) k1))
      (2 : u8));
  (pure (rust_primitives.hax.Tuple2.mk k1 k2))

@[spec]
def hkdf3 (key : (RustSlice u8)) (ikm : (RustSlice u8)) :
    RustM
    (rust_primitives.hax.Tuple3
      (alloc.vec.Vec u8 alloc.alloc.Global)
      (alloc.vec.Vec u8 alloc.alloc.Global)
      (alloc.vec.Vec u8 alloc.alloc.Global))
    := do
  let secret : (alloc.vec.Vec u8 alloc.alloc.Global) ← (hmac_hash key ikm);
  let k1 : (alloc.vec.Vec u8 alloc.alloc.Global) ←
    (kdf_next
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global) secret))
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global)
        (← (alloc.vec.Impl.new u8 rust_primitives.hax.Tuple0.mk))))
      (1 : u8));
  let k2 : (alloc.vec.Vec u8 alloc.alloc.Global) ←
    (kdf_next
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global) secret))
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global) k1))
      (2 : u8));
  let k3 : (alloc.vec.Vec u8 alloc.alloc.Global) ←
    (kdf_next
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global) secret))
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global) k1))
      (3 : u8));
  (pure (rust_primitives.hax.Tuple3.mk k1 k2 k3))

end new_tests.legacy__proverif_noise__lib.noise_crypto


namespace new_tests.legacy__proverif_noise__lib.noise_kkpsk0

structure ProtocolName where
  _0 : (RustArray u8 36)

def Noise_KKpsk0_25519_ChaChaPoly_SHA256 : ProtocolName :=
  RustM.of_isOk
    (do
    (ProtocolName.mk
      (RustArray.ofVec #v[(78 : u8),
                            (111 : u8),
                            (105 : u8),
                            (115 : u8),
                            (101 : u8),
                            (95 : u8),
                            (75 : u8),
                            (75 : u8),
                            (112 : u8),
                            (115 : u8),
                            (107 : u8),
                            (48 : u8),
                            (95 : u8),
                            (50 : u8),
                            (53 : u8),
                            (53 : u8),
                            (49 : u8),
                            (57 : u8),
                            (95 : u8),
                            (67 : u8),
                            (104 : u8),
                            (97 : u8),
                            (67 : u8),
                            (104 : u8),
                            (97 : u8),
                            (80 : u8),
                            (111 : u8),
                            (108 : u8),
                            (121 : u8),
                            (95 : u8),
                            (83 : u8),
                            (72 : u8),
                            (65 : u8),
                            (50 : u8),
                            (53 : u8),
                            (54 : u8)])))
    (by rfl)

end new_tests.legacy__proverif_noise__lib.noise_kkpsk0


namespace new_tests.legacy__proverif_noise__lib.noise_lib

--  This module defines the generic Noise processing rules
--  Section 5: https://noiseprotocol.org/noise.html#processing-rules
structure CipherState where
  k : (core_models.option.Option (alloc.vec.Vec u8 alloc.alloc.Global))
  n : u64

end new_tests.legacy__proverif_noise__lib.noise_lib


namespace new_tests.legacy__proverif_noise__lib.noise_kkpsk0

structure Transport where
  send : new_tests.legacy__proverif_noise__lib.noise_lib.CipherState
  recv : new_tests.legacy__proverif_noise__lib.noise_lib.CipherState
  handshake_hash : (alloc.vec.Vec u8 alloc.alloc.Global)

end new_tests.legacy__proverif_noise__lib.noise_kkpsk0


namespace new_tests.legacy__proverif_noise__lib.noise_lib

structure SymmetricState where
  cs : CipherState
  ck : (alloc.vec.Vec u8 alloc.alloc.Global)
  h : (alloc.vec.Vec u8 alloc.alloc.Global)

end new_tests.legacy__proverif_noise__lib.noise_lib


namespace new_tests.legacy__proverif_noise__lib.noise_kkpsk0

structure HandshakeStateI0 where
  st : new_tests.legacy__proverif_noise__lib.noise_lib.SymmetricState
  psk : (alloc.vec.Vec u8 alloc.alloc.Global)
  s : new_tests.legacy__proverif_noise__lib.noise_crypto.KeyPair
  e : new_tests.legacy__proverif_noise__lib.noise_crypto.KeyPair
  rs : (alloc.vec.Vec u8 alloc.alloc.Global)

structure HandshakeStateI1 where
  st : new_tests.legacy__proverif_noise__lib.noise_lib.SymmetricState
  s : new_tests.legacy__proverif_noise__lib.noise_crypto.KeyPair
  e : new_tests.legacy__proverif_noise__lib.noise_crypto.KeyPair

structure HandshakeStateR0 where
  st : new_tests.legacy__proverif_noise__lib.noise_lib.SymmetricState
  psk : (alloc.vec.Vec u8 alloc.alloc.Global)
  s : new_tests.legacy__proverif_noise__lib.noise_crypto.KeyPair
  e : new_tests.legacy__proverif_noise__lib.noise_crypto.KeyPair
  rs : (alloc.vec.Vec u8 alloc.alloc.Global)

structure HandshakeStateR1 where
  st : new_tests.legacy__proverif_noise__lib.noise_lib.SymmetricState
  e : new_tests.legacy__proverif_noise__lib.noise_crypto.KeyPair
  rs : (alloc.vec.Vec u8 alloc.alloc.Global)
  re : (alloc.vec.Vec u8 alloc.alloc.Global)

end new_tests.legacy__proverif_noise__lib.noise_kkpsk0


namespace new_tests.legacy__proverif_noise__lib.noise_lib

--  5.1: The CipherState Object
@[spec]
def initialize_key
    (key : (core_models.option.Option (alloc.vec.Vec u8 alloc.alloc.Global))) :
    RustM CipherState := do
  (pure (CipherState.mk (k := key) (n := (0 : u64))))

@[spec]
def has_key (cs : CipherState) : RustM Bool := do
  (core_models.option.Impl.is_some (alloc.vec.Vec u8 alloc.alloc.Global)
    (CipherState.k cs))

--  @fail(extraction): ssprove(HAX0001)
@[spec]
def set_nonce (cs : CipherState) (n : u64) : RustM CipherState := do
  let {k := k, n := _} := cs;
  (pure (CipherState.mk (k := k) (n := n)))

--  @fail(extraction): ssprove(HAX0001)
@[spec]
def encrypt_with_ad
    (cs : CipherState)
    (ad : (RustSlice u8))
    (plaintext : (RustSlice u8)) :
    RustM
    (core_models.result.Result
      (rust_primitives.hax.Tuple2
        CipherState
        (alloc.vec.Vec u8 alloc.alloc.Global))
      new_tests.legacy__proverif_noise__lib.noise_crypto.Error)
    := do
  let {k := k, n := n} := cs;
  if (← (n ==? (18446744073709551615 : u64))) then do
    (pure (core_models.result.Result.Err
      new_tests.legacy__proverif_noise__lib.noise_crypto.Error.CryptoError))
  else do
    match k with
      | (core_models.option.Option.Some  k) => do
        let cip : (alloc.vec.Vec u8 alloc.alloc.Global) ←
          (new_tests.legacy__proverif_noise__lib.noise_crypto.encrypt
            (← (core_models.ops.deref.Deref.deref
              (alloc.vec.Vec u8 alloc.alloc.Global) k))
            n
            ad
            plaintext);
        (pure (core_models.result.Result.Ok
          (rust_primitives.hax.Tuple2.mk
            (CipherState.mk
              (k := (core_models.option.Option.Some k))
              (n := (← (n +? (1 : u64)))))
            cip)))
      | (core_models.option.Option.None ) => do
        (pure (core_models.result.Result.Ok
          (rust_primitives.hax.Tuple2.mk
            (CipherState.mk (k := k) (n := n))
            (← (alloc.slice.Impl.to_vec u8 plaintext)))))

end new_tests.legacy__proverif_noise__lib.noise_lib


namespace new_tests.legacy__proverif_noise__lib.noise_kkpsk0

--   KKpsk0:
--     ->
--     <-
--  @fail(extraction): ssprove(HAX0001)
@[spec]
def write_transport
    (tx : Transport)
    (ad : (RustSlice u8))
    (payload : (RustSlice u8)) :
    RustM
    (core_models.result.Result
      (rust_primitives.hax.Tuple2
        Transport
        (alloc.vec.Vec u8 alloc.alloc.Global))
      new_tests.legacy__proverif_noise__lib.noise_crypto.Error)
    := do
  let {send := send, recv := recv, handshake_hash := handshake_hash} := tx;
  match
    (← (new_tests.legacy__proverif_noise__lib.noise_lib.encrypt_with_ad
      send
      ad
      payload))
  with
    | (core_models.result.Result.Ok  ⟨send, ciphertext⟩) => do
      let tx : Transport :=
        (Transport.mk
          (send := send)
          (recv := recv)
          (handshake_hash := handshake_hash));
      (pure (core_models.result.Result.Ok
        (rust_primitives.hax.Tuple2.mk tx ciphertext)))
    | (core_models.result.Result.Err  err) => do
      (pure (core_models.result.Result.Err err))

end new_tests.legacy__proverif_noise__lib.noise_kkpsk0


namespace new_tests.legacy__proverif_noise__lib.noise_lib

--  @fail(extraction): ssprove(HAX0001)
@[spec]
def decrypt_with_ad
    (cs : CipherState)
    (ad : (RustSlice u8))
    (ciphertext : (RustSlice u8)) :
    RustM
    (core_models.result.Result
      (rust_primitives.hax.Tuple2
        CipherState
        (alloc.vec.Vec u8 alloc.alloc.Global))
      new_tests.legacy__proverif_noise__lib.noise_crypto.Error)
    := do
  let {k := k, n := n} := cs;
  if (← (n ==? (18446744073709551615 : u64))) then do
    (pure (core_models.result.Result.Err
      new_tests.legacy__proverif_noise__lib.noise_crypto.Error.CryptoError))
  else do
    match k with
      | (core_models.option.Option.Some  k) => do
        match
          (← (new_tests.legacy__proverif_noise__lib.noise_crypto.decrypt
            (← (core_models.ops.deref.Deref.deref
              (alloc.vec.Vec u8 alloc.alloc.Global) k))
            n
            ad
            ciphertext))
        with
          | (core_models.result.Result.Ok  plain) => do
            (pure (core_models.result.Result.Ok
              (rust_primitives.hax.Tuple2.mk
                (CipherState.mk
                  (k := (core_models.option.Option.Some k))
                  (n := (← (n +? (1 : u64)))))
                plain)))
          | (core_models.result.Result.Err  err) => do
            (pure (core_models.result.Result.Err err))
      | (core_models.option.Option.None ) => do
        (pure (core_models.result.Result.Ok
          (rust_primitives.hax.Tuple2.mk
            (CipherState.mk (k := k) (n := n))
            (← (alloc.slice.Impl.to_vec u8 ciphertext)))))

end new_tests.legacy__proverif_noise__lib.noise_lib


namespace new_tests.legacy__proverif_noise__lib.noise_kkpsk0

--  @fail(extraction): ssprove(HAX0001)
@[spec]
def read_transport
    (tx : Transport)
    (ad : (RustSlice u8))
    (ciphertext : (RustSlice u8)) :
    RustM
    (core_models.result.Result
      (rust_primitives.hax.Tuple2
        Transport
        (alloc.vec.Vec u8 alloc.alloc.Global))
      new_tests.legacy__proverif_noise__lib.noise_crypto.Error)
    := do
  let {send := send, recv := recv, handshake_hash := handshake_hash} := tx;
  match
    (← (new_tests.legacy__proverif_noise__lib.noise_lib.decrypt_with_ad
      recv
      ad
      ciphertext))
  with
    | (core_models.result.Result.Ok  ⟨recv, payload⟩) => do
      let tx : Transport :=
        (Transport.mk
          (send := send)
          (recv := recv)
          (handshake_hash := handshake_hash));
      (pure (core_models.result.Result.Ok
        (rust_primitives.hax.Tuple2.mk tx payload)))
    | (core_models.result.Result.Err  err) => do
      (pure (core_models.result.Result.Err err))

end new_tests.legacy__proverif_noise__lib.noise_kkpsk0


namespace new_tests.legacy__proverif_noise__lib.noise_lib

--  @fail(extraction): ssprove(HAX0001)
@[spec]
def rekey (cs : CipherState) :
    RustM
    (core_models.result.Result
      CipherState
      new_tests.legacy__proverif_noise__lib.noise_crypto.Error)
    := do
  let {k := k, n := n} := cs;
  match k with
    | (core_models.option.Option.Some  k) => do
      let new_k : (alloc.vec.Vec u8 alloc.alloc.Global) ←
        (new_tests.legacy__proverif_noise__lib.noise_crypto.rekey
          (← (core_models.ops.deref.Deref.deref
            (alloc.vec.Vec u8 alloc.alloc.Global) k)));
      (pure (core_models.result.Result.Ok
        (CipherState.mk
          (k := (core_models.option.Option.Some new_k))
          (n := n))))
    | (core_models.option.Option.None ) => do
      (pure (core_models.result.Result.Err
        new_tests.legacy__proverif_noise__lib.noise_crypto.Error.CryptoError))

--  5.2: The SymmetricState Object
@[spec]
def initialize_symmetric (protocol_name : (RustSlice u8)) :
    RustM SymmetricState := do
  let pnlen : usize ← (core_models.slice.Impl.len u8 protocol_name);
  let hv : (alloc.vec.Vec u8 alloc.alloc.Global) ←
    if
    (← (pnlen <? new_tests.legacy__proverif_noise__lib.noise_crypto.HASHLEN))
    then do
      (alloc.slice.Impl.concat (RustSlice u8) u8
        (← (rust_primitives.unsize
          (RustArray.ofVec #v[protocol_name,
                                (← (core_models.ops.deref.Deref.deref
                                  (alloc.vec.Vec u8 alloc.alloc.Global)
                                  (← (alloc.vec.from_elem u8
                                    (0 : u8)
                                    (← ((32 : usize) -? pnlen))))))]))))
    else do
      (new_tests.legacy__proverif_noise__lib.noise_crypto.hash protocol_name);
  let ck : (alloc.vec.Vec u8 alloc.alloc.Global) ←
    (core_models.clone.Clone.clone (alloc.vec.Vec u8 alloc.alloc.Global) hv);
  (pure (SymmetricState.mk
    (cs := (← (initialize_key core_models.option.Option.None)))
    (ck := ck)
    (h := hv)))

--  @fail(extraction): ssprove(HAX0001)
@[spec]
def mix_key (st : SymmetricState) (input_key_material : (RustSlice u8)) :
    RustM SymmetricState := do
  let {cs := _, ck := ck, h := h} := st;
  let ⟨ck, temp_k⟩ ←
    (new_tests.legacy__proverif_noise__lib.noise_crypto.hkdf2
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global) ck))
      input_key_material);
  let temp_k : (alloc.vec.Vec u8 alloc.alloc.Global) ←
    if
    (← (new_tests.legacy__proverif_noise__lib.noise_crypto.HASHLEN
      ==? (64 : usize))) then do
      let temp_k : (alloc.vec.Vec u8 alloc.alloc.Global) ←
        (alloc.vec.Impl_1.truncate u8 alloc.alloc.Global temp_k (32 : usize));
      (pure temp_k)
    else do
      (pure temp_k);
  (pure (SymmetricState.mk
    (cs := (← (initialize_key (core_models.option.Option.Some temp_k))))
    (ck := ck)
    (h := h)))

--  @fail(extraction): ssprove(HAX0001)
@[spec]
def mix_hash (st : SymmetricState) (data : (RustSlice u8)) :
    RustM SymmetricState := do
  let {cs := cs, ck := ck, h := h} := st;
  (pure (SymmetricState.mk
    (cs := cs)
    (ck := ck)
    (h := (← (new_tests.legacy__proverif_noise__lib.noise_crypto.hash
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global)
        (← (alloc.slice.Impl.concat (RustSlice u8) u8
          (← (rust_primitives.unsize
            (RustArray.ofVec #v[(← (core_models.ops.deref.Deref.deref
                                    (alloc.vec.Vec u8 alloc.alloc.Global) h)),
                                  data]))))))))))))

end new_tests.legacy__proverif_noise__lib.noise_lib


namespace new_tests.legacy__proverif_noise__lib.noise_kkpsk0

--   KKpsk0:
--     -> s
--     <- s
--     ...
@[spec]
def initialize_initiator
    (prologue : (RustSlice u8))
    (psk : (alloc.vec.Vec u8 alloc.alloc.Global))
    (s : new_tests.legacy__proverif_noise__lib.noise_crypto.KeyPair)
    (e : new_tests.legacy__proverif_noise__lib.noise_crypto.KeyPair)
    (rs : (RustSlice u8)) :
    RustM HandshakeStateI0 := do
  let st : new_tests.legacy__proverif_noise__lib.noise_lib.SymmetricState ←
    (new_tests.legacy__proverif_noise__lib.noise_lib.initialize_symmetric
      (← (rust_primitives.unsize
        (ProtocolName._0 Noise_KKpsk0_25519_ChaChaPoly_SHA256))));
  let st : new_tests.legacy__proverif_noise__lib.noise_lib.SymmetricState ←
    (new_tests.legacy__proverif_noise__lib.noise_lib.mix_hash st prologue);
  let st : new_tests.legacy__proverif_noise__lib.noise_lib.SymmetricState ←
    (new_tests.legacy__proverif_noise__lib.noise_lib.mix_hash
      st
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global)
        (new_tests.legacy__proverif_noise__lib.noise_crypto.KeyPair.public_key
          s))));
  let st : new_tests.legacy__proverif_noise__lib.noise_lib.SymmetricState ←
    (new_tests.legacy__proverif_noise__lib.noise_lib.mix_hash st rs);
  (pure (HandshakeStateI0.mk
    (psk := psk)
    (st := st)
    (s := s)
    (e := e)
    (rs := (← (alloc.slice.Impl.to_vec u8 rs)))))

@[spec]
def initialize_responder
    (prologue : (RustSlice u8))
    (psk : (alloc.vec.Vec u8 alloc.alloc.Global))
    (s : new_tests.legacy__proverif_noise__lib.noise_crypto.KeyPair)
    (e : new_tests.legacy__proverif_noise__lib.noise_crypto.KeyPair)
    (rs : (RustSlice u8)) :
    RustM HandshakeStateR0 := do
  let st : new_tests.legacy__proverif_noise__lib.noise_lib.SymmetricState ←
    (new_tests.legacy__proverif_noise__lib.noise_lib.initialize_symmetric
      (← (rust_primitives.unsize
        (ProtocolName._0 Noise_KKpsk0_25519_ChaChaPoly_SHA256))));
  let st : new_tests.legacy__proverif_noise__lib.noise_lib.SymmetricState ←
    (new_tests.legacy__proverif_noise__lib.noise_lib.mix_hash st prologue);
  let st : new_tests.legacy__proverif_noise__lib.noise_lib.SymmetricState ←
    (new_tests.legacy__proverif_noise__lib.noise_lib.mix_hash st rs);
  let st : new_tests.legacy__proverif_noise__lib.noise_lib.SymmetricState ←
    (new_tests.legacy__proverif_noise__lib.noise_lib.mix_hash
      st
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global)
        (new_tests.legacy__proverif_noise__lib.noise_crypto.KeyPair.public_key
          s))));
  (pure (HandshakeStateR0.mk
    (st := st)
    (psk := psk)
    (s := s)
    (e := e)
    (rs := (← (alloc.slice.Impl.to_vec u8 rs)))))

end new_tests.legacy__proverif_noise__lib.noise_kkpsk0


namespace new_tests.legacy__proverif_noise__lib.noise_lib

--  @fail(extraction): ssprove(HAX0001)
@[spec]
def mix_key_and_hash
    (st : SymmetricState)
    (input_key_material : (RustSlice u8)) :
    RustM SymmetricState := do
  let {cs := _, ck := ck, h := h} := st;
  let ⟨ck, temp_h, temp_k⟩ ←
    (new_tests.legacy__proverif_noise__lib.noise_crypto.hkdf3
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global) ck))
      input_key_material);
  let new_h : (alloc.vec.Vec u8 alloc.alloc.Global) := h;
  let new_h : (alloc.vec.Vec u8 alloc.alloc.Global) ←
    (alloc.vec.Impl_2.extend_from_slice u8 alloc.alloc.Global
      new_h
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global) temp_h)));
  let new_h : (alloc.vec.Vec u8 alloc.alloc.Global) ←
    (new_tests.legacy__proverif_noise__lib.noise_crypto.hash
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global) new_h)));
  let temp_k : (alloc.vec.Vec u8 alloc.alloc.Global) ←
    if
    (← (new_tests.legacy__proverif_noise__lib.noise_crypto.HASHLEN
      ==? (64 : usize))) then do
      let temp_k : (alloc.vec.Vec u8 alloc.alloc.Global) ←
        (alloc.vec.Impl_1.truncate u8 alloc.alloc.Global temp_k (32 : usize));
      (pure temp_k)
    else do
      (pure temp_k);
  (pure (SymmetricState.mk
    (cs := (← (initialize_key (core_models.option.Option.Some temp_k))))
    (ck := ck)
    (h := new_h)))

--  Unclear if we need a special function for psk or we can reuse mix_key_and_hash above
@[spec]
def encrypt_and_hash (st : SymmetricState) (plaintext : (RustSlice u8)) :
    RustM
    (core_models.result.Result
      (rust_primitives.hax.Tuple2
        SymmetricState
        (alloc.vec.Vec u8 alloc.alloc.Global))
      new_tests.legacy__proverif_noise__lib.noise_crypto.Error)
    := do
  match
    (← (encrypt_with_ad
      (SymmetricState.cs st)
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global) (SymmetricState.h st)))
      plaintext))
  with
    | (core_models.result.Result.Ok  ⟨new_cs, ciphertext⟩) => do
      let new_h : (alloc.vec.Vec u8 alloc.alloc.Global) ←
        (core_models.clone.Clone.clone
          (alloc.vec.Vec u8 alloc.alloc.Global) (SymmetricState.h st));
      let new_h : (alloc.vec.Vec u8 alloc.alloc.Global) ←
        (alloc.vec.Impl_2.extend_from_slice u8 alloc.alloc.Global
          new_h
          (← (core_models.ops.deref.Deref.deref
            (alloc.vec.Vec u8 alloc.alloc.Global) ciphertext)));
      let new_h : (alloc.vec.Vec u8 alloc.alloc.Global) ←
        (new_tests.legacy__proverif_noise__lib.noise_crypto.hash
          (← (core_models.ops.deref.Deref.deref
            (alloc.vec.Vec u8 alloc.alloc.Global) new_h)));
      (pure (core_models.result.Result.Ok
        (rust_primitives.hax.Tuple2.mk
          (SymmetricState.mk
            (cs := new_cs)
            (ck := (SymmetricState.ck st))
            (h := new_h))
          ciphertext)))
    | (core_models.result.Result.Err  err) => do
      (pure (core_models.result.Result.Err err))

end new_tests.legacy__proverif_noise__lib.noise_lib


namespace new_tests.legacy__proverif_noise__lib.noise_kkpsk0

--   KKpsk0:
--     ...
--     -> psk, e, es, ss
--  @fail(extraction): ssprove(HAX0001)
@[spec]
def write_message1 (hs : HandshakeStateI0) (payload : (RustSlice u8)) :
    RustM
    (core_models.result.Result
      (rust_primitives.hax.Tuple2
        HandshakeStateI1
        (alloc.vec.Vec u8 alloc.alloc.Global))
      new_tests.legacy__proverif_noise__lib.noise_crypto.Error)
    := do
  let {st := st, psk := psk, s := s, e := e, rs := rs} := hs;
  let st : new_tests.legacy__proverif_noise__lib.noise_lib.SymmetricState ←
    (new_tests.legacy__proverif_noise__lib.noise_lib.mix_key_and_hash
      st
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global) psk)));
  let st : new_tests.legacy__proverif_noise__lib.noise_lib.SymmetricState ←
    (new_tests.legacy__proverif_noise__lib.noise_lib.mix_hash
      st
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global)
        (new_tests.legacy__proverif_noise__lib.noise_crypto.KeyPair.public_key
          e))));
  let st : new_tests.legacy__proverif_noise__lib.noise_lib.SymmetricState ←
    (new_tests.legacy__proverif_noise__lib.noise_lib.mix_key
      st
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global)
        (new_tests.legacy__proverif_noise__lib.noise_crypto.KeyPair.public_key
          e))));
  let es : (alloc.vec.Vec u8 alloc.alloc.Global) ←
    (new_tests.legacy__proverif_noise__lib.noise_crypto.dh
      e
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global) rs)));
  let st : new_tests.legacy__proverif_noise__lib.noise_lib.SymmetricState ←
    (new_tests.legacy__proverif_noise__lib.noise_lib.mix_key
      st
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global) es)));
  let ss : (alloc.vec.Vec u8 alloc.alloc.Global) ←
    (new_tests.legacy__proverif_noise__lib.noise_crypto.dh
      s
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global) rs)));
  let st : new_tests.legacy__proverif_noise__lib.noise_lib.SymmetricState ←
    (new_tests.legacy__proverif_noise__lib.noise_lib.mix_key
      st
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global) ss)));
  match
    (← (new_tests.legacy__proverif_noise__lib.noise_lib.encrypt_and_hash
      st
      payload))
  with
    | (core_models.result.Result.Ok  ⟨st, ciphertext⟩) => do
      let hs : HandshakeStateI1 :=
        (HandshakeStateI1.mk (st := st) (s := s) (e := e));
      (pure (core_models.result.Result.Ok
        (rust_primitives.hax.Tuple2.mk hs ciphertext)))
    | (core_models.result.Result.Err  err) => do
      (pure (core_models.result.Result.Err err))

end new_tests.legacy__proverif_noise__lib.noise_kkpsk0


namespace new_tests.legacy__proverif_noise__lib.noise_lib

@[spec]
def decrypt_and_hash (st : SymmetricState) (ciphertext : (RustSlice u8)) :
    RustM
    (core_models.result.Result
      (rust_primitives.hax.Tuple2
        SymmetricState
        (alloc.vec.Vec u8 alloc.alloc.Global))
      new_tests.legacy__proverif_noise__lib.noise_crypto.Error)
    := do
  match
    (← (decrypt_with_ad
      (SymmetricState.cs st)
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global) (SymmetricState.h st)))
      ciphertext))
  with
    | (core_models.result.Result.Ok  ⟨new_cs, plaintext⟩) => do
      let new_h : (alloc.vec.Vec u8 alloc.alloc.Global) ←
        (core_models.clone.Clone.clone
          (alloc.vec.Vec u8 alloc.alloc.Global) (SymmetricState.h st));
      let new_h : (alloc.vec.Vec u8 alloc.alloc.Global) ←
        (alloc.vec.Impl_2.extend_from_slice u8 alloc.alloc.Global
          new_h
          ciphertext);
      let new_h : (alloc.vec.Vec u8 alloc.alloc.Global) ←
        (new_tests.legacy__proverif_noise__lib.noise_crypto.hash
          (← (core_models.ops.deref.Deref.deref
            (alloc.vec.Vec u8 alloc.alloc.Global) new_h)));
      (pure (core_models.result.Result.Ok
        (rust_primitives.hax.Tuple2.mk
          (SymmetricState.mk
            (cs := new_cs)
            (ck := (SymmetricState.ck st))
            (h := new_h))
          plaintext)))
    | (core_models.result.Result.Err  err) => do
      (pure (core_models.result.Result.Err err))

end new_tests.legacy__proverif_noise__lib.noise_lib


namespace new_tests.legacy__proverif_noise__lib.noise_kkpsk0

--  @fail(extraction): ssprove(HAX0001)
@[spec]
def read_message1 (hs : HandshakeStateR0) (ciphertext : (RustSlice u8)) :
    RustM
    (core_models.result.Result
      (rust_primitives.hax.Tuple2
        HandshakeStateR1
        (alloc.vec.Vec u8 alloc.alloc.Global))
      new_tests.legacy__proverif_noise__lib.noise_crypto.Error)
    := do
  let {st := st, psk := psk, s := s, e := e, rs := rs} := hs;
  let re : (RustSlice u8) ←
    ciphertext[
      (core_models.ops.range.Range.mk
        (start := (0 : usize))
        (_end := new_tests.legacy__proverif_noise__lib.noise_crypto.DHLEN))
      ]_?;
  let ciphertext : (RustSlice u8) ←
    ciphertext[
      (core_models.ops.range.Range.mk
        (start := new_tests.legacy__proverif_noise__lib.noise_crypto.DHLEN)
        (_end := (← (core_models.slice.Impl.len u8 ciphertext))))
      ]_?;
  let st : new_tests.legacy__proverif_noise__lib.noise_lib.SymmetricState ←
    (new_tests.legacy__proverif_noise__lib.noise_lib.mix_key_and_hash
      st
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global) psk)));
  let st : new_tests.legacy__proverif_noise__lib.noise_lib.SymmetricState ←
    (new_tests.legacy__proverif_noise__lib.noise_lib.mix_hash st re);
  let st : new_tests.legacy__proverif_noise__lib.noise_lib.SymmetricState ←
    (new_tests.legacy__proverif_noise__lib.noise_lib.mix_key st re);
  let es : (alloc.vec.Vec u8 alloc.alloc.Global) ←
    (new_tests.legacy__proverif_noise__lib.noise_crypto.dh s re);
  let st : new_tests.legacy__proverif_noise__lib.noise_lib.SymmetricState ←
    (new_tests.legacy__proverif_noise__lib.noise_lib.mix_key
      st
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global) es)));
  let ss : (alloc.vec.Vec u8 alloc.alloc.Global) ←
    (new_tests.legacy__proverif_noise__lib.noise_crypto.dh
      s
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global) rs)));
  let st : new_tests.legacy__proverif_noise__lib.noise_lib.SymmetricState ←
    (new_tests.legacy__proverif_noise__lib.noise_lib.mix_key
      st
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global) ss)));
  match
    (← (new_tests.legacy__proverif_noise__lib.noise_lib.decrypt_and_hash
      st
      ciphertext))
  with
    | (core_models.result.Result.Ok  ⟨st, plaintext⟩) => do
      let hs : HandshakeStateR1 :=
        (HandshakeStateR1.mk
          (st := st)
          (e := e)
          (rs := rs)
          (re := (← (alloc.slice.Impl.to_vec u8 re))));
      (pure (core_models.result.Result.Ok
        (rust_primitives.hax.Tuple2.mk hs plaintext)))
    | (core_models.result.Result.Err  err) => do
      (pure (core_models.result.Result.Err err))

end new_tests.legacy__proverif_noise__lib.noise_kkpsk0


namespace new_tests.legacy__proverif_noise__lib.noise_lib

@[spec]
def split (st : SymmetricState) :
    RustM
    (rust_primitives.hax.Tuple3
      CipherState
      CipherState
      (alloc.vec.Vec u8 alloc.alloc.Global))
    := do
  let ⟨temp_k1, temp_k2⟩ ←
    (new_tests.legacy__proverif_noise__lib.noise_crypto.hkdf2
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global) (SymmetricState.ck st)))
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global)
        (← (alloc.vec.Impl.new u8 rust_primitives.hax.Tuple0.mk)))));
  let ⟨temp_k1, temp_k2⟩ ←
    if
    (← (new_tests.legacy__proverif_noise__lib.noise_crypto.HASHLEN
      ==? (64 : usize))) then do
      let temp_k1 : (alloc.vec.Vec u8 alloc.alloc.Global) ←
        (alloc.vec.Impl_1.truncate u8 alloc.alloc.Global temp_k1 (32 : usize));
      let temp_k2 : (alloc.vec.Vec u8 alloc.alloc.Global) ←
        (alloc.vec.Impl_1.truncate u8 alloc.alloc.Global temp_k2 (32 : usize));
      (pure (rust_primitives.hax.Tuple2.mk temp_k1 temp_k2))
    else do
      (pure (rust_primitives.hax.Tuple2.mk temp_k1 temp_k2));
  (pure (rust_primitives.hax.Tuple3.mk
    (← (initialize_key (core_models.option.Option.Some temp_k1)))
    (← (initialize_key (core_models.option.Option.Some temp_k2)))
    (SymmetricState.h st)))

end new_tests.legacy__proverif_noise__lib.noise_lib


namespace new_tests.legacy__proverif_noise__lib.noise_kkpsk0

--   KKpsk0:
--     ...
--      <- e, ee, se
--  @fail(extraction): ssprove(HAX0001)
@[spec]
def write_message2 (hs : HandshakeStateR1) (payload : (RustSlice u8)) :
    RustM
    (core_models.result.Result
      (rust_primitives.hax.Tuple2
        Transport
        (alloc.vec.Vec u8 alloc.alloc.Global))
      new_tests.legacy__proverif_noise__lib.noise_crypto.Error)
    := do
  let {st := st, e := e, rs := rs, re := re} := hs;
  let st : new_tests.legacy__proverif_noise__lib.noise_lib.SymmetricState ←
    (new_tests.legacy__proverif_noise__lib.noise_lib.mix_hash
      st
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global)
        (new_tests.legacy__proverif_noise__lib.noise_crypto.KeyPair.public_key
          e))));
  let st : new_tests.legacy__proverif_noise__lib.noise_lib.SymmetricState ←
    (new_tests.legacy__proverif_noise__lib.noise_lib.mix_key
      st
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global)
        (new_tests.legacy__proverif_noise__lib.noise_crypto.KeyPair.public_key
          e))));
  let ee : (alloc.vec.Vec u8 alloc.alloc.Global) ←
    (new_tests.legacy__proverif_noise__lib.noise_crypto.dh
      e
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global) re)));
  let st : new_tests.legacy__proverif_noise__lib.noise_lib.SymmetricState ←
    (new_tests.legacy__proverif_noise__lib.noise_lib.mix_key
      st
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global) ee)));
  let se : (alloc.vec.Vec u8 alloc.alloc.Global) ←
    (new_tests.legacy__proverif_noise__lib.noise_crypto.dh
      e
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global) rs)));
  let st : new_tests.legacy__proverif_noise__lib.noise_lib.SymmetricState ←
    (new_tests.legacy__proverif_noise__lib.noise_lib.mix_key
      st
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global) se)));
  match
    (← (new_tests.legacy__proverif_noise__lib.noise_lib.encrypt_and_hash
      st
      payload))
  with
    | (core_models.result.Result.Ok  ⟨st, ciphertext⟩) => do
      let ⟨c1, c2, h⟩ ←
        (new_tests.legacy__proverif_noise__lib.noise_lib.split st);
      let tx : Transport :=
        (Transport.mk (send := c2) (recv := c1) (handshake_hash := h));
      (pure (core_models.result.Result.Ok
        (rust_primitives.hax.Tuple2.mk tx ciphertext)))
    | (core_models.result.Result.Err  err) => do
      (pure (core_models.result.Result.Err err))

--  @fail(extraction): ssprove(HAX0001)
@[spec]
def read_message2 (hs : HandshakeStateI1) (ciphertext : (RustSlice u8)) :
    RustM
    (core_models.result.Result
      (rust_primitives.hax.Tuple2
        Transport
        (alloc.vec.Vec u8 alloc.alloc.Global))
      new_tests.legacy__proverif_noise__lib.noise_crypto.Error)
    := do
  let {st := st, s := s, e := e} := hs;
  let re : (RustSlice u8) ←
    ciphertext[
      (core_models.ops.range.Range.mk
        (start := (0 : usize))
        (_end := new_tests.legacy__proverif_noise__lib.noise_crypto.DHLEN))
      ]_?;
  let ciphertext : (RustSlice u8) ←
    ciphertext[
      (core_models.ops.range.Range.mk
        (start := new_tests.legacy__proverif_noise__lib.noise_crypto.DHLEN)
        (_end := (← (core_models.slice.Impl.len u8 ciphertext))))
      ]_?;
  let st : new_tests.legacy__proverif_noise__lib.noise_lib.SymmetricState ←
    (new_tests.legacy__proverif_noise__lib.noise_lib.mix_hash st re);
  let st : new_tests.legacy__proverif_noise__lib.noise_lib.SymmetricState ←
    (new_tests.legacy__proverif_noise__lib.noise_lib.mix_key st re);
  let ee : (alloc.vec.Vec u8 alloc.alloc.Global) ←
    (new_tests.legacy__proverif_noise__lib.noise_crypto.dh e re);
  let st : new_tests.legacy__proverif_noise__lib.noise_lib.SymmetricState ←
    (new_tests.legacy__proverif_noise__lib.noise_lib.mix_key
      st
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global) ee)));
  let se : (alloc.vec.Vec u8 alloc.alloc.Global) ←
    (new_tests.legacy__proverif_noise__lib.noise_crypto.dh s re);
  let st : new_tests.legacy__proverif_noise__lib.noise_lib.SymmetricState ←
    (new_tests.legacy__proverif_noise__lib.noise_lib.mix_key
      st
      (← (core_models.ops.deref.Deref.deref
        (alloc.vec.Vec u8 alloc.alloc.Global) se)));
  match
    (← (new_tests.legacy__proverif_noise__lib.noise_lib.decrypt_and_hash
      st
      ciphertext))
  with
    | (core_models.result.Result.Ok  ⟨st, plaintext⟩) => do
      let ⟨c1, c2, h⟩ ←
        (new_tests.legacy__proverif_noise__lib.noise_lib.split st);
      let tx : Transport :=
        (Transport.mk (send := c1) (recv := c2) (handshake_hash := h));
      (pure (core_models.result.Result.Ok
        (rust_primitives.hax.Tuple2.mk tx plaintext)))
    | (core_models.result.Result.Err  err) => do
      (pure (core_models.result.Result.Err err))

end new_tests.legacy__proverif_noise__lib.noise_kkpsk0

