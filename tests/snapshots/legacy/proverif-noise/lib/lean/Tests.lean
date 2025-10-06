
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

inductive Tests.Legacy__proverif_noise__lib.Noise_crypto.Error : Type
| CryptoError : Tests.Legacy__proverif_noise__lib.Noise_crypto.Error 


def Tests.Legacy__proverif_noise__lib.Noise_crypto.Error
  (x : Tests.Legacy__proverif_noise__lib.Noise_crypto.Error)
  : Result isize
  := do
  (match x with
    | (Tests.Legacy__proverif_noise__lib.Noise_crypto.Error.CryptoError )
      => do (0 : isize))

structure Tests.Legacy__proverif_noise__lib.Noise_crypto.KeyPair where
  private_key : Hax_lib_protocol.Crypto.DHScalar
  public_key : (Alloc.Vec.Vec u8 Alloc.Alloc.Global)

def Tests.Legacy__proverif_noise__lib.Noise_crypto.DHLEN : usize := 32

def Tests.Legacy__proverif_noise__lib.Noise_crypto.generate_keypair
  (sk : (RustSlice u8))
  : Result Tests.Legacy__proverif_noise__lib.Noise_crypto.KeyPair
  := do
  let sk : Hax_lib_protocol.Crypto.DHScalar ← (pure
    (← Hax_lib_protocol.Crypto.Impl.from_bytes sk));
  let pk : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← Hax_lib_protocol.Crypto.dh_scalar_multiply_base
        Hax_lib_protocol.Crypto.DHGroup.X25519
        (← Core.Clone.Clone.clone sk)));
  (Tests.Legacy__proverif_noise__lib.Noise_crypto.KeyPair.mk
    (private_key := sk) (public_key := pk))

def Tests.Legacy__proverif_noise__lib.Noise_crypto.dh
  (sk : Tests.Legacy__proverif_noise__lib.Noise_crypto.KeyPair)
  (pk : (RustSlice u8))
  : Result (Alloc.Vec.Vec u8 Alloc.Alloc.Global)
  := do
  let pk : Hax_lib_protocol.Crypto.DHElement ← (pure
    (← Hax_lib_protocol.Crypto.Impl_1.from_bytes pk));
  (← Hax_lib_protocol.Crypto.dh_scalar_multiply
      Hax_lib_protocol.Crypto.DHGroup.X25519
      (← Core.Clone.Clone.clone
          (Tests.Legacy__proverif_noise__lib.Noise_crypto.KeyPair.private_key
              sk))
      pk)

def Tests.Legacy__proverif_noise__lib.Noise_crypto.encrypt
  (key : (RustSlice u8))
  (counter : u64)
  (aad : (RustSlice u8))
  (plain : (RustSlice u8))
  : Result (Alloc.Vec.Vec u8 Alloc.Alloc.Global)
  := do
  let chacha_iv : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← Alloc.Vec.from_elem u8 (0 : u8) (4 : usize)));
  let chacha_iv : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← Alloc.Vec.Impl_2.extend_from_slice u8 Alloc.Alloc.Global
        chacha_iv
        (← Rust_primitives.unsize (← Core.Num.Impl_9.to_le_bytes counter))));
  let ⟨cipher, tag⟩ ← (pure
    (← Hax_lib_protocol.Crypto.aead_encrypt
        (← Hax_lib_protocol.Crypto.Impl_4.from_bytes
            Hax_lib_protocol.Crypto.AEADAlgorithm.Chacha20Poly1305
            key)
        (← Hax_lib_protocol.Crypto.Impl_5.from_bytes
            (← Core.Ops.Deref.Deref.deref chacha_iv))
        aad
        plain));
  let cipher : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← Alloc.Vec.Impl_2.extend_from_slice u8 Alloc.Alloc.Global
        cipher
        (← Core.Ops.Deref.Deref.deref tag)));
  cipher

def Tests.Legacy__proverif_noise__lib.Noise_crypto.decrypt
  (key : (RustSlice u8))
  (counter : u64)
  (aad : (RustSlice u8))
  (cipher : (RustSlice u8))
  : Result
  (Core.Result.Result
    (Alloc.Vec.Vec u8 Alloc.Alloc.Global)
    Tests.Legacy__proverif_noise__lib.Noise_crypto.Error)
  := do
  let chacha_iv : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← Alloc.Vec.from_elem u8 (0 : u8) (4 : usize)));
  let chacha_iv : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← Alloc.Vec.Impl_2.extend_from_slice u8 Alloc.Alloc.Global
        chacha_iv
        (← Rust_primitives.unsize (← Core.Num.Impl_9.to_le_bytes counter))));
  let cipher_len : usize ← (pure
    (← (← Core.Slice.Impl.len u8 cipher) -? (16 : usize)));
  let cip : (RustSlice u8) ← (pure
    (← Core.Ops.Index.Index.index
        cipher
        (Core.Ops.Range.Range.mk (start := (0 : usize)) (_end := cipher_len))));
  let tag : (RustSlice u8) ← (pure
    (← Core.Ops.Index.Index.index
        cipher
        (Core.Ops.Range.Range.mk
          (start := cipher_len) (_end := (← Core.Slice.Impl.len u8 cipher)))));
  (← Core.Result.Impl.map_err
      (Alloc.Vec.Vec u8 Alloc.Alloc.Global)
      Hax_lib_protocol.ProtocolError
      Tests.Legacy__proverif_noise__lib.Noise_crypto.Error
      Hax_lib_protocol.ProtocolError
      -> Result Tests.Legacy__proverif_noise__lib.Noise_crypto.Error
      (← Hax_lib_protocol.Crypto.aead_decrypt
          (← Hax_lib_protocol.Crypto.Impl_4.from_bytes
              Hax_lib_protocol.Crypto.AEADAlgorithm.Chacha20Poly1305
              key)
          (← Hax_lib_protocol.Crypto.Impl_5.from_bytes
              (← Core.Ops.Deref.Deref.deref chacha_iv))
          aad
          cip
          (← Hax_lib_protocol.Crypto.Impl_6.from_bytes tag))
      (fun _ => (do
          Tests.Legacy__proverif_noise__lib.Noise_crypto.Error.CryptoError :
          Result Tests.Legacy__proverif_noise__lib.Noise_crypto.Error)))

def Tests.Legacy__proverif_noise__lib.Noise_crypto.rekey
  (key : (RustSlice u8))
  : Result (Alloc.Vec.Vec u8 Alloc.Alloc.Global)
  := do
  (← Tests.Legacy__proverif_noise__lib.Noise_crypto.encrypt
      key
      (18446744073709551615 : u64)
      (← Core.Ops.Deref.Deref.deref
          (← Alloc.Vec.Impl.new u8 Rust_primitives.Hax.Tuple0.mk))
      (← Rust_primitives.unsize
          (← Rust_primitives.Hax.repeat (0 : u8) (32 : usize))))

def Tests.Legacy__proverif_noise__lib.Noise_crypto.HASHLEN : usize := 32

def Tests.Legacy__proverif_noise__lib.Noise_crypto.BLOCKLEN : usize := 64

def Tests.Legacy__proverif_noise__lib.Noise_crypto.hash
  (input : (RustSlice u8))
  : Result (Alloc.Vec.Vec u8 Alloc.Alloc.Global)
  := do
  (← Hax_lib_protocol.Crypto.hash
      Hax_lib_protocol.Crypto.HashAlgorithm.Sha256
      input)

def Tests.Legacy__proverif_noise__lib.Noise_crypto.hmac_hash
  (key : (RustSlice u8))
  (input : (RustSlice u8))
  : Result (Alloc.Vec.Vec u8 Alloc.Alloc.Global)
  := do
  (← Hax_lib_protocol.Crypto.hmac
      Hax_lib_protocol.Crypto.HMACAlgorithm.Sha256
      key
      input)

def Tests.Legacy__proverif_noise__lib.Noise_crypto.kdf_next
  (secret : (RustSlice u8))
  (prev : (RustSlice u8))
  (counter : u8)
  : Result (Alloc.Vec.Vec u8 Alloc.Alloc.Global)
  := do
  (← Tests.Legacy__proverif_noise__lib.Noise_crypto.hmac_hash
      secret
      (← Core.Ops.Deref.Deref.deref
          (← Alloc.Slice.Impl.concat (RustSlice u8) u8
              (← Rust_primitives.unsize
                  #v[prev, (← Rust_primitives.unsize #v[counter])]))))

def Tests.Legacy__proverif_noise__lib.Noise_crypto.hkdf1
  (key : (RustSlice u8))
  (ikm : (RustSlice u8))
  : Result (Alloc.Vec.Vec u8 Alloc.Alloc.Global)
  := do
  let secret : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_crypto.hmac_hash key ikm));
  (← Tests.Legacy__proverif_noise__lib.Noise_crypto.kdf_next
      (← Core.Ops.Deref.Deref.deref secret)
      (← Core.Ops.Deref.Deref.deref
          (← Alloc.Vec.Impl.new u8 Rust_primitives.Hax.Tuple0.mk))
      (1 : u8))

def Tests.Legacy__proverif_noise__lib.Noise_crypto.hkdf2
  (key : (RustSlice u8))
  (ikm : (RustSlice u8))
  : Result
  (Rust_primitives.Hax.Tuple2
    (Alloc.Vec.Vec u8 Alloc.Alloc.Global)
    (Alloc.Vec.Vec u8 Alloc.Alloc.Global))
  := do
  let secret : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_crypto.hmac_hash key ikm));
  let k1 : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_crypto.kdf_next
        (← Core.Ops.Deref.Deref.deref secret)
        (← Core.Ops.Deref.Deref.deref
            (← Alloc.Vec.Impl.new u8 Rust_primitives.Hax.Tuple0.mk))
        (1 : u8)));
  let k2 : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_crypto.kdf_next
        (← Core.Ops.Deref.Deref.deref secret)
        (← Core.Ops.Deref.Deref.deref k1)
        (2 : u8)));
  (Rust_primitives.Hax.Tuple2.mk k1 k2)

def Tests.Legacy__proverif_noise__lib.Noise_crypto.hkdf3
  (key : (RustSlice u8))
  (ikm : (RustSlice u8))
  : Result
  (Rust_primitives.Hax.Tuple3
    (Alloc.Vec.Vec u8 Alloc.Alloc.Global)
    (Alloc.Vec.Vec u8 Alloc.Alloc.Global)
    (Alloc.Vec.Vec u8 Alloc.Alloc.Global))
  := do
  let secret : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_crypto.hmac_hash key ikm));
  let k1 : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_crypto.kdf_next
        (← Core.Ops.Deref.Deref.deref secret)
        (← Core.Ops.Deref.Deref.deref
            (← Alloc.Vec.Impl.new u8 Rust_primitives.Hax.Tuple0.mk))
        (1 : u8)));
  let k2 : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_crypto.kdf_next
        (← Core.Ops.Deref.Deref.deref secret)
        (← Core.Ops.Deref.Deref.deref k1)
        (2 : u8)));
  let k3 : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_crypto.kdf_next
        (← Core.Ops.Deref.Deref.deref secret)
        (← Core.Ops.Deref.Deref.deref k1)
        (3 : u8)));
  (Rust_primitives.Hax.Tuple3.mk k1 k2 k3)

structure Tests.Legacy__proverif_noise__lib.Noise_lib.CipherState where
  k : (Core.Option.Option (Alloc.Vec.Vec u8 Alloc.Alloc.Global))
  n : u64

structure Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState where
  cs : Tests.Legacy__proverif_noise__lib.Noise_lib.CipherState
  ck : (Alloc.Vec.Vec u8 Alloc.Alloc.Global)
  h : (Alloc.Vec.Vec u8 Alloc.Alloc.Global)

def Tests.Legacy__proverif_noise__lib.Noise_lib.initialize_key
  (key : (Core.Option.Option (Alloc.Vec.Vec u8 Alloc.Alloc.Global)))
  : Result Tests.Legacy__proverif_noise__lib.Noise_lib.CipherState
  := do
  (Tests.Legacy__proverif_noise__lib.Noise_lib.CipherState.mk
    (k := key) (n := (0 : u64)))

def Tests.Legacy__proverif_noise__lib.Noise_lib.has_key
  (cs : Tests.Legacy__proverif_noise__lib.Noise_lib.CipherState)
  : Result Bool
  := do
  (← Core.Option.Impl.is_some (Alloc.Vec.Vec u8 Alloc.Alloc.Global)
      (Tests.Legacy__proverif_noise__lib.Noise_lib.CipherState.k cs))

def Tests.Legacy__proverif_noise__lib.Noise_lib.set_nonce
  (cs : Tests.Legacy__proverif_noise__lib.Noise_lib.CipherState)
  (n : u64)
  : Result Tests.Legacy__proverif_noise__lib.Noise_lib.CipherState
  := do
  let {k := k, n := _} ← (pure cs);
  (Tests.Legacy__proverif_noise__lib.Noise_lib.CipherState.mk (k := k) (n := n))

def Tests.Legacy__proverif_noise__lib.Noise_lib.encrypt_with_ad
  (cs : Tests.Legacy__proverif_noise__lib.Noise_lib.CipherState)
  (ad : (RustSlice u8))
  (plaintext : (RustSlice u8))
  : Result
  (Core.Result.Result
    (Rust_primitives.Hax.Tuple2
      Tests.Legacy__proverif_noise__lib.Noise_lib.CipherState
      (Alloc.Vec.Vec u8 Alloc.Alloc.Global))
    Tests.Legacy__proverif_noise__lib.Noise_crypto.Error)
  := do
  let {k := k, n := n} ← (pure cs);
  (← if
  (← Rust_primitives.Hax.Machine_int.eq n (18446744073709551615 : u64)) then do
    (Core.Result.Result.Err
      Tests.Legacy__proverif_noise__lib.Noise_crypto.Error.CryptoError)
  else do
    (match k with
      | (Core.Option.Option.Some k)
        => do
          let cip : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
            (← Tests.Legacy__proverif_noise__lib.Noise_crypto.encrypt
                (← Core.Ops.Deref.Deref.deref k)
                n
                ad
                plaintext));
          (Core.Result.Result.Ok
            (Rust_primitives.Hax.Tuple2.mk
              (Tests.Legacy__proverif_noise__lib.Noise_lib.CipherState.mk
                (k := (Core.Option.Option.Some k)) (n := (← n +? (1 : u64))))
              cip))
      | (Core.Option.Option.None )
        => do
          (Core.Result.Result.Ok
            (Rust_primitives.Hax.Tuple2.mk
              (Tests.Legacy__proverif_noise__lib.Noise_lib.CipherState.mk
                (k := k) (n := n))
              (← Alloc.Slice.Impl.to_vec u8 plaintext)))))

def Tests.Legacy__proverif_noise__lib.Noise_lib.decrypt_with_ad
  (cs : Tests.Legacy__proverif_noise__lib.Noise_lib.CipherState)
  (ad : (RustSlice u8))
  (ciphertext : (RustSlice u8))
  : Result
  (Core.Result.Result
    (Rust_primitives.Hax.Tuple2
      Tests.Legacy__proverif_noise__lib.Noise_lib.CipherState
      (Alloc.Vec.Vec u8 Alloc.Alloc.Global))
    Tests.Legacy__proverif_noise__lib.Noise_crypto.Error)
  := do
  let {k := k, n := n} ← (pure cs);
  (← if
  (← Rust_primitives.Hax.Machine_int.eq n (18446744073709551615 : u64)) then do
    (Core.Result.Result.Err
      Tests.Legacy__proverif_noise__lib.Noise_crypto.Error.CryptoError)
  else do
    (match k with
      | (Core.Option.Option.Some k)
        => do
          (match
            (← Tests.Legacy__proverif_noise__lib.Noise_crypto.decrypt
                (← Core.Ops.Deref.Deref.deref k)
                n
                ad
                ciphertext)
          with
            | (Core.Result.Result.Ok plain)
              => do
                (Core.Result.Result.Ok
                  (Rust_primitives.Hax.Tuple2.mk
                    (Tests.Legacy__proverif_noise__lib.Noise_lib.CipherState.mk
                      (k := (Core.Option.Option.Some k))
                      (n := (← n +? (1 : u64))))
                    plain))
            | (Core.Result.Result.Err err) => do (Core.Result.Result.Err err))
      | (Core.Option.Option.None )
        => do
          (Core.Result.Result.Ok
            (Rust_primitives.Hax.Tuple2.mk
              (Tests.Legacy__proverif_noise__lib.Noise_lib.CipherState.mk
                (k := k) (n := n))
              (← Alloc.Slice.Impl.to_vec u8 ciphertext)))))

def Tests.Legacy__proverif_noise__lib.Noise_lib.rekey
  (cs : Tests.Legacy__proverif_noise__lib.Noise_lib.CipherState)
  : Result
  (Core.Result.Result
    Tests.Legacy__proverif_noise__lib.Noise_lib.CipherState
    Tests.Legacy__proverif_noise__lib.Noise_crypto.Error)
  := do
  let {k := k, n := n} ← (pure cs);
  (match k with
    | (Core.Option.Option.Some k)
      => do
        let new_k : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
          (← Tests.Legacy__proverif_noise__lib.Noise_crypto.rekey
              (← Core.Ops.Deref.Deref.deref k)));
        (Core.Result.Result.Ok
          (Tests.Legacy__proverif_noise__lib.Noise_lib.CipherState.mk
            (k := (Core.Option.Option.Some new_k)) (n := n)))
    | (Core.Option.Option.None )
      => do
        (Core.Result.Result.Err
          Tests.Legacy__proverif_noise__lib.Noise_crypto.Error.CryptoError))

def Tests.Legacy__proverif_noise__lib.Noise_lib.initialize_symmetric
  (protocol_name : (RustSlice u8))
  : Result Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState
  := do
  let pnlen : usize ← (pure (← Core.Slice.Impl.len u8 protocol_name));
  let hv ← (pure
    (← if
    (← Rust_primitives.Hax.Machine_int.lt
        pnlen
        Tests.Legacy__proverif_noise__lib.Noise_crypto.HASHLEN) then do
      (← Alloc.Slice.Impl.concat (RustSlice u8) u8
          (← Rust_primitives.unsize
              #v[protocol_name,
                   (← Core.Ops.Deref.Deref.deref
                       (← Alloc.Vec.from_elem u8
                           (0 : u8)
                           (← (32 : usize) -? pnlen)))]))
    else do
      (← Tests.Legacy__proverif_noise__lib.Noise_crypto.hash protocol_name)));
  let ck : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← Core.Clone.Clone.clone hv));
  (Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState.mk
    (cs := (← Tests.Legacy__proverif_noise__lib.Noise_lib.initialize_key
        Core.Option.Option.None))
    (ck := ck)
    (h := hv))

def Tests.Legacy__proverif_noise__lib.Noise_lib.mix_key
  (st : Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState)
  (input_key_material : (RustSlice u8))
  : Result Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState
  := do
  let {cs := _, ck := ck, h := h} ← (pure st);
  let ⟨ck, temp_k⟩ ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_crypto.hkdf2
        (← Core.Ops.Deref.Deref.deref ck)
        input_key_material));
  let temp_k : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← if
    (← Rust_primitives.Hax.Machine_int.eq
        Tests.Legacy__proverif_noise__lib.Noise_crypto.HASHLEN
        (64 : usize)) then do
      let temp_k : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
        (← Alloc.Vec.Impl_1.truncate u8 Alloc.Alloc.Global
            temp_k
            (32 : usize)));
      temp_k
    else do
      temp_k));
  (Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState.mk
    (cs := (← Tests.Legacy__proverif_noise__lib.Noise_lib.initialize_key
        (Core.Option.Option.Some temp_k)))
    (ck := ck)
    (h := h))

def Tests.Legacy__proverif_noise__lib.Noise_lib.mix_hash
  (st : Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState)
  (data : (RustSlice u8))
  : Result Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState
  := do
  let {cs := cs, ck := ck, h := h} ← (pure st);
  (Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState.mk
    (cs := cs)
    (ck := ck)
    (h := (← Tests.Legacy__proverif_noise__lib.Noise_crypto.hash
        (← Core.Ops.Deref.Deref.deref
            (← Alloc.Slice.Impl.concat (RustSlice u8) u8
                (← Rust_primitives.unsize
                    #v[(← Core.Ops.Deref.Deref.deref h), data]))))))

def Tests.Legacy__proverif_noise__lib.Noise_lib.mix_key_and_hash
  (st : Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState)
  (input_key_material : (RustSlice u8))
  : Result Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState
  := do
  let {cs := _, ck := ck, h := h} ← (pure st);
  let ⟨ck, temp_h, temp_k⟩ ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_crypto.hkdf3
        (← Core.Ops.Deref.Deref.deref ck)
        input_key_material));
  let new_h : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure h);
  let new_h : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← Alloc.Vec.Impl_2.extend_from_slice u8 Alloc.Alloc.Global
        new_h
        (← Core.Ops.Deref.Deref.deref temp_h)));
  let new_h : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_crypto.hash
        (← Core.Ops.Deref.Deref.deref new_h)));
  let temp_k : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← if
    (← Rust_primitives.Hax.Machine_int.eq
        Tests.Legacy__proverif_noise__lib.Noise_crypto.HASHLEN
        (64 : usize)) then do
      let temp_k : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
        (← Alloc.Vec.Impl_1.truncate u8 Alloc.Alloc.Global
            temp_k
            (32 : usize)));
      temp_k
    else do
      temp_k));
  (Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState.mk
    (cs := (← Tests.Legacy__proverif_noise__lib.Noise_lib.initialize_key
        (Core.Option.Option.Some temp_k)))
    (ck := ck)
    (h := new_h))

def Tests.Legacy__proverif_noise__lib.Noise_lib.encrypt_and_hash
  (st : Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState)
  (plaintext : (RustSlice u8))
  : Result
  (Core.Result.Result
    (Rust_primitives.Hax.Tuple2
      Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState
      (Alloc.Vec.Vec u8 Alloc.Alloc.Global))
    Tests.Legacy__proverif_noise__lib.Noise_crypto.Error)
  := do
  (match
    (← Tests.Legacy__proverif_noise__lib.Noise_lib.encrypt_with_ad
        (Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState.cs st)
        (← Core.Ops.Deref.Deref.deref
            (Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState.h st))
        plaintext)
  with
    | (Core.Result.Result.Ok ⟨new_cs, ciphertext⟩)
      => do
        let new_h : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
          (← Core.Clone.Clone.clone
              (Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState.h
                  st)));
        let new_h : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
          (← Alloc.Vec.Impl_2.extend_from_slice u8 Alloc.Alloc.Global
              new_h
              (← Core.Ops.Deref.Deref.deref ciphertext)));
        let new_h : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
          (← Tests.Legacy__proverif_noise__lib.Noise_crypto.hash
              (← Core.Ops.Deref.Deref.deref new_h)));
        (Core.Result.Result.Ok
          (Rust_primitives.Hax.Tuple2.mk
            (Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState.mk
              (cs := new_cs)
              (ck :=
              (Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState.ck
                  st))
              (h := new_h))
            ciphertext))
    | (Core.Result.Result.Err err) => do (Core.Result.Result.Err err))

def Tests.Legacy__proverif_noise__lib.Noise_lib.decrypt_and_hash
  (st : Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState)
  (ciphertext : (RustSlice u8))
  : Result
  (Core.Result.Result
    (Rust_primitives.Hax.Tuple2
      Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState
      (Alloc.Vec.Vec u8 Alloc.Alloc.Global))
    Tests.Legacy__proverif_noise__lib.Noise_crypto.Error)
  := do
  (match
    (← Tests.Legacy__proverif_noise__lib.Noise_lib.decrypt_with_ad
        (Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState.cs st)
        (← Core.Ops.Deref.Deref.deref
            (Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState.h st))
        ciphertext)
  with
    | (Core.Result.Result.Ok ⟨new_cs, plaintext⟩)
      => do
        let new_h : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
          (← Core.Clone.Clone.clone
              (Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState.h
                  st)));
        let new_h : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
          (← Alloc.Vec.Impl_2.extend_from_slice u8 Alloc.Alloc.Global
              new_h
              ciphertext));
        let new_h : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
          (← Tests.Legacy__proverif_noise__lib.Noise_crypto.hash
              (← Core.Ops.Deref.Deref.deref new_h)));
        (Core.Result.Result.Ok
          (Rust_primitives.Hax.Tuple2.mk
            (Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState.mk
              (cs := new_cs)
              (ck :=
              (Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState.ck
                  st))
              (h := new_h))
            plaintext))
    | (Core.Result.Result.Err err) => do (Core.Result.Result.Err err))

def Tests.Legacy__proverif_noise__lib.Noise_lib.split
  (st : Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState)
  : Result
  (Rust_primitives.Hax.Tuple3
    Tests.Legacy__proverif_noise__lib.Noise_lib.CipherState
    Tests.Legacy__proverif_noise__lib.Noise_lib.CipherState
    (Alloc.Vec.Vec u8 Alloc.Alloc.Global))
  := do
  let ⟨temp_k1, temp_k2⟩ ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_crypto.hkdf2
        (← Core.Ops.Deref.Deref.deref
            (Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState.ck st))
        (← Core.Ops.Deref.Deref.deref
            (← Alloc.Vec.Impl.new u8 Rust_primitives.Hax.Tuple0.mk))));
  let ⟨temp_k1, temp_k2⟩ ← (pure
    (← if
    (← Rust_primitives.Hax.Machine_int.eq
        Tests.Legacy__proverif_noise__lib.Noise_crypto.HASHLEN
        (64 : usize)) then do
      let temp_k1 : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
        (← Alloc.Vec.Impl_1.truncate u8 Alloc.Alloc.Global
            temp_k1
            (32 : usize)));
      let temp_k2 : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
        (← Alloc.Vec.Impl_1.truncate u8 Alloc.Alloc.Global
            temp_k2
            (32 : usize)));
      (Rust_primitives.Hax.Tuple2.mk temp_k1 temp_k2)
    else do
      (Rust_primitives.Hax.Tuple2.mk temp_k1 temp_k2)));
  (Rust_primitives.Hax.Tuple3.mk
    (← Tests.Legacy__proverif_noise__lib.Noise_lib.initialize_key
        (Core.Option.Option.Some temp_k1))
    (← Tests.Legacy__proverif_noise__lib.Noise_lib.initialize_key
        (Core.Option.Option.Some temp_k2))
    (Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState.h st))

structure Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.HandshakeStateI0 where
  st : Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState
  psk : (Alloc.Vec.Vec u8 Alloc.Alloc.Global)
  s : Tests.Legacy__proverif_noise__lib.Noise_crypto.KeyPair
  e : Tests.Legacy__proverif_noise__lib.Noise_crypto.KeyPair
  rs : (Alloc.Vec.Vec u8 Alloc.Alloc.Global)

structure Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.HandshakeStateI1 where
  st : Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState
  s : Tests.Legacy__proverif_noise__lib.Noise_crypto.KeyPair
  e : Tests.Legacy__proverif_noise__lib.Noise_crypto.KeyPair

structure Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.HandshakeStateR0 where
  st : Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState
  psk : (Alloc.Vec.Vec u8 Alloc.Alloc.Global)
  s : Tests.Legacy__proverif_noise__lib.Noise_crypto.KeyPair
  e : Tests.Legacy__proverif_noise__lib.Noise_crypto.KeyPair
  rs : (Alloc.Vec.Vec u8 Alloc.Alloc.Global)

structure Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.HandshakeStateR1 where
  st : Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState
  e : Tests.Legacy__proverif_noise__lib.Noise_crypto.KeyPair
  rs : (Alloc.Vec.Vec u8 Alloc.Alloc.Global)
  re : (Alloc.Vec.Vec u8 Alloc.Alloc.Global)

structure Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.Transport where
  send : Tests.Legacy__proverif_noise__lib.Noise_lib.CipherState
  recv : Tests.Legacy__proverif_noise__lib.Noise_lib.CipherState
  handshake_hash : (Alloc.Vec.Vec u8 Alloc.Alloc.Global)

structure Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.ProtocolName where
  _0 : (RustArray u8 (36 : usize))

def
  Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.Noise_KKpsk0_25519_ChaChaPoly_SHA256
  : Result Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.ProtocolName
  := do
  (Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.ProtocolName.mk
    #v[(78 : u8),
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
         (54 : u8)])

def Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.initialize_initiator
  (prologue : (RustSlice u8))
  (psk : (Alloc.Vec.Vec u8 Alloc.Alloc.Global))
  (s : Tests.Legacy__proverif_noise__lib.Noise_crypto.KeyPair)
  (e : Tests.Legacy__proverif_noise__lib.Noise_crypto.KeyPair)
  (rs : (RustSlice u8))
  : Result Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.HandshakeStateI0
  := do
  let st : Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_lib.initialize_symmetric
        (← Rust_primitives.unsize
            (Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.ProtocolName._0
                Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.Noise_KKpsk0_25519_ChaChaPoly_SHA256))));
  let st : Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_lib.mix_hash st prologue));
  let st : Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_lib.mix_hash
        st
        (← Core.Ops.Deref.Deref.deref
            (Tests.Legacy__proverif_noise__lib.Noise_crypto.KeyPair.public_key
                s))));
  let st : Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_lib.mix_hash st rs));
  (Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.HandshakeStateI0.mk
    (psk := psk)
    (st := st)
    (s := s)
    (e := e)
    (rs := (← Alloc.Slice.Impl.to_vec u8 rs)))

def Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.initialize_responder
  (prologue : (RustSlice u8))
  (psk : (Alloc.Vec.Vec u8 Alloc.Alloc.Global))
  (s : Tests.Legacy__proverif_noise__lib.Noise_crypto.KeyPair)
  (e : Tests.Legacy__proverif_noise__lib.Noise_crypto.KeyPair)
  (rs : (RustSlice u8))
  : Result Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.HandshakeStateR0
  := do
  let st : Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_lib.initialize_symmetric
        (← Rust_primitives.unsize
            (Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.ProtocolName._0
                Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.Noise_KKpsk0_25519_ChaChaPoly_SHA256))));
  let st : Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_lib.mix_hash st prologue));
  let st : Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_lib.mix_hash st rs));
  let st : Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_lib.mix_hash
        st
        (← Core.Ops.Deref.Deref.deref
            (Tests.Legacy__proverif_noise__lib.Noise_crypto.KeyPair.public_key
                s))));
  (Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.HandshakeStateR0.mk
    (st := st)
    (psk := psk)
    (s := s)
    (e := e)
    (rs := (← Alloc.Slice.Impl.to_vec u8 rs)))

def Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.write_message1
  (hs : Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.HandshakeStateI0)
  (payload : (RustSlice u8))
  : Result
  (Core.Result.Result
    (Rust_primitives.Hax.Tuple2
      Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.HandshakeStateI1
      (Alloc.Vec.Vec u8 Alloc.Alloc.Global))
    Tests.Legacy__proverif_noise__lib.Noise_crypto.Error)
  := do
  let {st := st, psk := psk, s := s, e := e, rs := rs} ← (pure hs);
  let st : Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_lib.mix_key_and_hash
        st
        (← Core.Ops.Deref.Deref.deref psk)));
  let st : Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_lib.mix_hash
        st
        (← Core.Ops.Deref.Deref.deref
            (Tests.Legacy__proverif_noise__lib.Noise_crypto.KeyPair.public_key
                e))));
  let st : Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_lib.mix_key
        st
        (← Core.Ops.Deref.Deref.deref
            (Tests.Legacy__proverif_noise__lib.Noise_crypto.KeyPair.public_key
                e))));
  let es : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_crypto.dh
        e
        (← Core.Ops.Deref.Deref.deref rs)));
  let st : Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_lib.mix_key
        st
        (← Core.Ops.Deref.Deref.deref es)));
  let ss : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_crypto.dh
        s
        (← Core.Ops.Deref.Deref.deref rs)));
  let st : Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_lib.mix_key
        st
        (← Core.Ops.Deref.Deref.deref ss)));
  (match
    (← Tests.Legacy__proverif_noise__lib.Noise_lib.encrypt_and_hash st payload)
  with
    | (Core.Result.Result.Ok ⟨st, ciphertext⟩)
      => do
        let
          hs : Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.HandshakeStateI1 ←
          (pure
          (Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.HandshakeStateI1.mk
            (st := st) (s := s) (e := e)));
        (Core.Result.Result.Ok (Rust_primitives.Hax.Tuple2.mk hs ciphertext))
    | (Core.Result.Result.Err err) => do (Core.Result.Result.Err err))

def Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.read_message1
  (hs : Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.HandshakeStateR0)
  (ciphertext : (RustSlice u8))
  : Result
  (Core.Result.Result
    (Rust_primitives.Hax.Tuple2
      Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.HandshakeStateR1
      (Alloc.Vec.Vec u8 Alloc.Alloc.Global))
    Tests.Legacy__proverif_noise__lib.Noise_crypto.Error)
  := do
  let {st := st, psk := psk, s := s, e := e, rs := rs} ← (pure hs);
  let re : (RustSlice u8) ← (pure
    (← Core.Ops.Index.Index.index
        ciphertext
        (Core.Ops.Range.Range.mk
          (start := (0 : usize))
          (_end := Tests.Legacy__proverif_noise__lib.Noise_crypto.DHLEN))));
  let ciphertext : (RustSlice u8) ← (pure
    (← Core.Ops.Index.Index.index
        ciphertext
        (Core.Ops.Range.Range.mk
          (start := Tests.Legacy__proverif_noise__lib.Noise_crypto.DHLEN)
          (_end := (← Core.Slice.Impl.len u8 ciphertext)))));
  let st : Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_lib.mix_key_and_hash
        st
        (← Core.Ops.Deref.Deref.deref psk)));
  let st : Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_lib.mix_hash st re));
  let st : Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_lib.mix_key st re));
  let es : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_crypto.dh s re));
  let st : Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_lib.mix_key
        st
        (← Core.Ops.Deref.Deref.deref es)));
  let ss : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_crypto.dh
        s
        (← Core.Ops.Deref.Deref.deref rs)));
  let st : Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_lib.mix_key
        st
        (← Core.Ops.Deref.Deref.deref ss)));
  (match
    (← Tests.Legacy__proverif_noise__lib.Noise_lib.decrypt_and_hash
        st
        ciphertext)
  with
    | (Core.Result.Result.Ok ⟨st, plaintext⟩)
      => do
        let
          hs : Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.HandshakeStateR1 ←
          (pure
          (Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.HandshakeStateR1.mk
            (st := st)
            (e := e)
            (rs := rs)
            (re := (← Alloc.Slice.Impl.to_vec u8 re))));
        (Core.Result.Result.Ok (Rust_primitives.Hax.Tuple2.mk hs plaintext))
    | (Core.Result.Result.Err err) => do (Core.Result.Result.Err err))

def Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.write_message2
  (hs : Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.HandshakeStateR1)
  (payload : (RustSlice u8))
  : Result
  (Core.Result.Result
    (Rust_primitives.Hax.Tuple2
      Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.Transport
      (Alloc.Vec.Vec u8 Alloc.Alloc.Global))
    Tests.Legacy__proverif_noise__lib.Noise_crypto.Error)
  := do
  let {st := st, e := e, rs := rs, re := re} ← (pure hs);
  let st : Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_lib.mix_hash
        st
        (← Core.Ops.Deref.Deref.deref
            (Tests.Legacy__proverif_noise__lib.Noise_crypto.KeyPair.public_key
                e))));
  let st : Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_lib.mix_key
        st
        (← Core.Ops.Deref.Deref.deref
            (Tests.Legacy__proverif_noise__lib.Noise_crypto.KeyPair.public_key
                e))));
  let ee : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_crypto.dh
        e
        (← Core.Ops.Deref.Deref.deref re)));
  let st : Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_lib.mix_key
        st
        (← Core.Ops.Deref.Deref.deref ee)));
  let se : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_crypto.dh
        e
        (← Core.Ops.Deref.Deref.deref rs)));
  let st : Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_lib.mix_key
        st
        (← Core.Ops.Deref.Deref.deref se)));
  (match
    (← Tests.Legacy__proverif_noise__lib.Noise_lib.encrypt_and_hash st payload)
  with
    | (Core.Result.Result.Ok ⟨st, ciphertext⟩)
      => do
        let ⟨c1, c2, h⟩ ← (pure
          (← Tests.Legacy__proverif_noise__lib.Noise_lib.split st));
        let tx : Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.Transport ←
          (pure
          (Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.Transport.mk
            (send := c2) (recv := c1) (handshake_hash := h)));
        (Core.Result.Result.Ok (Rust_primitives.Hax.Tuple2.mk tx ciphertext))
    | (Core.Result.Result.Err err) => do (Core.Result.Result.Err err))

def Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.read_message2
  (hs : Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.HandshakeStateI1)
  (ciphertext : (RustSlice u8))
  : Result
  (Core.Result.Result
    (Rust_primitives.Hax.Tuple2
      Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.Transport
      (Alloc.Vec.Vec u8 Alloc.Alloc.Global))
    Tests.Legacy__proverif_noise__lib.Noise_crypto.Error)
  := do
  let {st := st, s := s, e := e} ← (pure hs);
  let re : (RustSlice u8) ← (pure
    (← Core.Ops.Index.Index.index
        ciphertext
        (Core.Ops.Range.Range.mk
          (start := (0 : usize))
          (_end := Tests.Legacy__proverif_noise__lib.Noise_crypto.DHLEN))));
  let ciphertext : (RustSlice u8) ← (pure
    (← Core.Ops.Index.Index.index
        ciphertext
        (Core.Ops.Range.Range.mk
          (start := Tests.Legacy__proverif_noise__lib.Noise_crypto.DHLEN)
          (_end := (← Core.Slice.Impl.len u8 ciphertext)))));
  let st : Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_lib.mix_hash st re));
  let st : Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_lib.mix_key st re));
  let ee : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_crypto.dh e re));
  let st : Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_lib.mix_key
        st
        (← Core.Ops.Deref.Deref.deref ee)));
  let se : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_crypto.dh s re));
  let st : Tests.Legacy__proverif_noise__lib.Noise_lib.SymmetricState ← (pure
    (← Tests.Legacy__proverif_noise__lib.Noise_lib.mix_key
        st
        (← Core.Ops.Deref.Deref.deref se)));
  (match
    (← Tests.Legacy__proverif_noise__lib.Noise_lib.decrypt_and_hash
        st
        ciphertext)
  with
    | (Core.Result.Result.Ok ⟨st, plaintext⟩)
      => do
        let ⟨c1, c2, h⟩ ← (pure
          (← Tests.Legacy__proverif_noise__lib.Noise_lib.split st));
        let tx : Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.Transport ←
          (pure
          (Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.Transport.mk
            (send := c1) (recv := c2) (handshake_hash := h)));
        (Core.Result.Result.Ok (Rust_primitives.Hax.Tuple2.mk tx plaintext))
    | (Core.Result.Result.Err err) => do (Core.Result.Result.Err err))

def Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.write_transport
  (tx : Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.Transport)
  (ad : (RustSlice u8))
  (payload : (RustSlice u8))
  : Result
  (Core.Result.Result
    (Rust_primitives.Hax.Tuple2
      Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.Transport
      (Alloc.Vec.Vec u8 Alloc.Alloc.Global))
    Tests.Legacy__proverif_noise__lib.Noise_crypto.Error)
  := do
  let {send := send, recv := recv, handshake_hash := handshake_hash} ← (pure
    tx);
  (match
    (← Tests.Legacy__proverif_noise__lib.Noise_lib.encrypt_with_ad
        send
        ad
        payload)
  with
    | (Core.Result.Result.Ok ⟨send, ciphertext⟩)
      => do
        let tx : Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.Transport ←
          (pure
          (Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.Transport.mk
            (send := send) (recv := recv) (handshake_hash := handshake_hash)));
        (Core.Result.Result.Ok (Rust_primitives.Hax.Tuple2.mk tx ciphertext))
    | (Core.Result.Result.Err err) => do (Core.Result.Result.Err err))

def Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.read_transport
  (tx : Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.Transport)
  (ad : (RustSlice u8))
  (ciphertext : (RustSlice u8))
  : Result
  (Core.Result.Result
    (Rust_primitives.Hax.Tuple2
      Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.Transport
      (Alloc.Vec.Vec u8 Alloc.Alloc.Global))
    Tests.Legacy__proverif_noise__lib.Noise_crypto.Error)
  := do
  let {send := send, recv := recv, handshake_hash := handshake_hash} ← (pure
    tx);
  (match
    (← Tests.Legacy__proverif_noise__lib.Noise_lib.decrypt_with_ad
        recv
        ad
        ciphertext)
  with
    | (Core.Result.Result.Ok ⟨recv, payload⟩)
      => do
        let tx : Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.Transport ←
          (pure
          (Tests.Legacy__proverif_noise__lib.Noise_kkpsk0.Transport.mk
            (send := send) (recv := recv) (handshake_hash := handshake_hash)));
        (Core.Result.Result.Ok (Rust_primitives.Hax.Tuple2.mk tx payload))
    | (Core.Result.Result.Err err) => do (Core.Result.Result.Err err))