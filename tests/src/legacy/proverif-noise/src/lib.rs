pub mod noise_crypto {
    // Import hacspec and all needed definitions.
    use hax_lib_protocol::crypto::{DHGroup, *};

    /// This file formalizes the Crypto Functions from the Noise Specification
    /// Section 4: Crypto Functions
    /// https://noiseprotocol.org/noise.html#crypto-functions

    pub enum Error {
        CryptoError,
    }

    /// Section 4.1 and 12.1: Diffie-Hellman Functions for Curve25519
    pub struct KeyPair {
        private_key: DHScalar,
        pub public_key: Vec<u8>,
    }

    pub const DHLEN: usize = 32;

    pub fn generate_keypair(sk: &[u8]) -> KeyPair {
        let sk = DHScalar::from_bytes(sk);
        let pk = dh_scalar_multiply_base(DHGroup::X25519, sk.clone());
        KeyPair {
            private_key: sk,
            public_key: pk,
        }
    }

    pub fn dh(sk: &KeyPair, pk: &[u8]) -> Vec<u8> {
        let pk = DHElement::from_bytes(pk);

        dh_scalar_multiply(DHGroup::X25519, sk.private_key.clone(), pk)
    }

    /// Section 4.2 and 12.3: Cipher functions for ChaCha20-Poly1305

    pub fn encrypt(key: &[u8], counter: u64, aad: &[u8], plain: &[u8]) -> Vec<u8> {
        let mut chacha_iv = vec![0u8; 4];
        chacha_iv.extend_from_slice(&counter.to_le_bytes());
        let (mut cipher, tag) = aead_encrypt(
            AEADKey::from_bytes(AEADAlgorithm::Chacha20Poly1305, key),
            AEADIV::from_bytes(&chacha_iv),
            aad,
            plain,
        );
        cipher.extend_from_slice(&tag);
        cipher
    }

    pub fn decrypt(key: &[u8], counter: u64, aad: &[u8], cipher: &[u8]) -> Result<Vec<u8>, Error> {
        let mut chacha_iv = vec![0u8; 4];
        chacha_iv.extend_from_slice(&counter.to_le_bytes());
        let cipher_len = cipher.len() - 16;
        let cip = &cipher[0..cipher_len];
        let tag = &cipher[cipher_len..cipher.len()];
        aead_decrypt(
            AEADKey::from_bytes(AEADAlgorithm::Chacha20Poly1305, key),
            AEADIV::from_bytes(&chacha_iv),
            aad,
            cip,
            AEADTag::from_bytes(tag),
        )
        .map_err(|_| Error::CryptoError)
    }

    pub fn rekey(key: &[u8]) -> Vec<u8> {
        encrypt(key, 0xffffffffffffffffu64, &Vec::new(), &[0u8; 32])
    }

    /// Section 4.3 and 12.5: Hash functions for SHA-256

    pub const HASHLEN: usize = 32;
    pub const BLOCKLEN: usize = 64;

    pub fn hash(input: &[u8]) -> Vec<u8> {
        hax_lib_protocol::crypto::hash(HashAlgorithm::Sha256, input)
    }

    pub fn hmac_hash(key: &[u8], input: &[u8]) -> Vec<u8> {
        hmac(HMACAlgorithm::Sha256, key, input)
    }

    /// HKDF spec as per Noise
    /// Alternative would be to directly use HKDF

    pub fn kdf_next(secret: &[u8], prev: &[u8], counter: u8) -> Vec<u8> {
        hmac_hash(secret, &[prev, &[counter]].concat())
    }

    pub fn hkdf1(key: &[u8], ikm: &[u8]) -> Vec<u8> {
        let secret = hmac_hash(key, ikm);
        kdf_next(&secret, &Vec::new(), 1)
    }

    pub fn hkdf2(key: &[u8], ikm: &[u8]) -> (Vec<u8>, Vec<u8>) {
        let secret = hmac_hash(key, ikm);
        let k1 = kdf_next(&secret, &Vec::new(), 1);
        let k2 = kdf_next(&secret, &k1, 2);
        (k1, k2)
    }

    pub fn hkdf3(key: &[u8], ikm: &[u8]) -> (Vec<u8>, Vec<u8>, Vec<u8>) {
        let secret = hmac_hash(key, ikm);
        let k1 = kdf_next(&secret, &Vec::new(), 1);
        let k2 = kdf_next(&secret, &k1, 2);
        let k3 = kdf_next(&secret, &k1, 3);
        (k1, k2, k3)
    }
}
pub mod noise_kkpsk0 {
    // Import hacspec and all needed definitions.
    use super::*;
    use noise_crypto::*;
    use noise_lib::*;

    pub struct HandshakeStateI0 {
        st: SymmetricState,
        psk: Vec<u8>,
        s: KeyPair,
        e: KeyPair,
        rs: Vec<u8>,
    }

    pub struct HandshakeStateI1 {
        st: SymmetricState,
        s: KeyPair,
        e: KeyPair,
    }

    pub struct HandshakeStateR0 {
        st: SymmetricState,
        psk: Vec<u8>,
        s: KeyPair,
        e: KeyPair,
        rs: Vec<u8>,
    }

    pub struct HandshakeStateR1 {
        st: SymmetricState,
        e: KeyPair,
        rs: Vec<u8>,
        re: Vec<u8>,
    }

    pub struct Transport {
        send: CipherState,
        recv: CipherState,
        handshake_hash: Vec<u8>,
    }

    struct ProtocolName([u8; 36]);
    #[allow(non_upper_case_globals)]
    const Noise_KKpsk0_25519_ChaChaPoly_SHA256: ProtocolName = ProtocolName([
        78u8, 111u8, 105u8, 115u8, 101u8, 95u8, 75u8, 75u8, 112u8, 115u8, 107u8, 48u8, 95u8, 50u8,
        53u8, 53u8, 49u8, 57u8, 95u8, 67u8, 104u8, 97u8, 67u8, 104u8, 97u8, 80u8, 111u8, 108u8,
        121u8, 95u8, 83u8, 72u8, 65u8, 50u8, 53u8, 54u8,
    ]);

    ///  KKpsk0:
    ///    -> s
    ///    <- s
    ///    ...
    pub fn initialize_initiator(
        prologue: &[u8],
        psk: Vec<u8>,
        s: KeyPair,
        e: KeyPair,
        rs: &[u8],
    ) -> HandshakeStateI0 {
        let st = initialize_symmetric(&Noise_KKpsk0_25519_ChaChaPoly_SHA256.0);
        let st = mix_hash(st, prologue);
        let st = mix_hash(st, &s.public_key);
        let st = mix_hash(st, rs);
        HandshakeStateI0 {
            psk,
            st,
            s,
            e,
            rs: rs.to_vec(),
        }
    }

    pub fn initialize_responder(
        prologue: &[u8],
        psk: Vec<u8>,
        s: KeyPair,
        e: KeyPair,
        rs: &[u8],
    ) -> HandshakeStateR0 {
        let st = initialize_symmetric(&Noise_KKpsk0_25519_ChaChaPoly_SHA256.0);
        let st = mix_hash(st, prologue);
        let st = mix_hash(st, rs);
        let st = mix_hash(st, &s.public_key);
        HandshakeStateR0 {
            st,
            psk,
            s,
            e,
            rs: rs.to_vec(),
        }
    }

    ///  KKpsk0:
    ///    ...
    ///    -> psk, e, es, ss
    pub fn write_message1(
        hs: HandshakeStateI0,
        payload: &[u8],
    ) -> Result<(HandshakeStateI1, Vec<u8>), Error> {
        let HandshakeStateI0 { st, psk, s, e, rs } = hs;
        let st = mix_key_and_hash(st, &psk);
        let st = mix_hash(st, &e.public_key);
        let st = mix_key(st, &e.public_key);
        let es = dh(&e, &rs);
        let st = mix_key(st, &es);
        let ss = dh(&s, &rs);
        let st = mix_key(st, &ss);
        let (st, ciphertext) = encrypt_and_hash(st, payload)?;
        let hs = HandshakeStateI1 { st, s, e };
        Ok((hs, ciphertext))
    }

    pub fn read_message1(
        hs: HandshakeStateR0,
        ciphertext: &[u8],
    ) -> Result<(HandshakeStateR1, Vec<u8>), Error> {
        let HandshakeStateR0 { st, psk, s, e, rs } = hs;
        let re = &ciphertext[0..DHLEN];
        let ciphertext = &ciphertext[DHLEN..ciphertext.len()];
        let st = mix_key_and_hash(st, &psk);
        let st = mix_hash(st, re);
        let st = mix_key(st, re);
        let es = dh(&s, re);
        let st = mix_key(st, &es);
        let ss = dh(&s, &rs);
        let st = mix_key(st, &ss);
        let (st, plaintext) = decrypt_and_hash(st, ciphertext)?;
        let hs = HandshakeStateR1 {
            st,
            e,
            rs,
            re: re.to_vec(),
        };
        Ok((hs, plaintext))
    }

    ///  KKpsk0:
    ///    ...
    ///     <- e, ee, se
    pub fn write_message2(
        hs: HandshakeStateR1,
        payload: &[u8],
    ) -> Result<(Transport, Vec<u8>), Error> {
        let HandshakeStateR1 { st, e, rs, re } = hs;
        let st = mix_hash(st, &e.public_key);
        let st = mix_key(st, &e.public_key);
        let ee = dh(&e, &re);
        let st = mix_key(st, &ee);
        let se = dh(&e, &rs);
        let st = mix_key(st, &se);
        let (st, ciphertext) = encrypt_and_hash(st, payload)?;
        let (c1, c2, h) = split(st);
        let tx = Transport {
            send: c2,
            recv: c1,
            handshake_hash: h,
        };
        Ok((tx, ciphertext))
    }

    pub fn read_message2(
        hs: HandshakeStateI1,
        ciphertext: &[u8],
    ) -> Result<(Transport, Vec<u8>), Error> {
        let HandshakeStateI1 { st, s, e } = hs;
        let re = &ciphertext[0..DHLEN];
        let ciphertext = &ciphertext[DHLEN..ciphertext.len()];
        let st = mix_hash(st, re);
        let st = mix_key(st, re);
        let ee = dh(&e, re);
        let st = mix_key(st, &ee);
        let se = dh(&s, re);
        let st = mix_key(st, &se);
        let (st, plaintext) = decrypt_and_hash(st, ciphertext)?;
        let (c1, c2, h) = split(st);
        let tx = Transport {
            send: c1,
            recv: c2,
            handshake_hash: h,
        };
        Ok((tx, plaintext))
    }

    ///  KKpsk0:
    ///    ->
    ///    <-
    pub fn write_transport(
        tx: Transport,
        ad: &[u8],
        payload: &[u8],
    ) -> Result<(Transport, Vec<u8>), Error> {
        let Transport {
            send,
            recv,
            handshake_hash,
        } = tx;
        let (send, ciphertext) = encrypt_with_ad(send, ad, payload)?;
        let tx = Transport {
            send,
            recv,
            handshake_hash,
        };
        Ok((tx, ciphertext))
    }

    pub fn read_transport(
        tx: Transport,
        ad: &[u8],
        ciphertext: &[u8],
    ) -> Result<(Transport, Vec<u8>), Error> {
        let Transport {
            send,
            recv,
            handshake_hash,
        } = tx;
        let (recv, payload) = decrypt_with_ad(recv, ad, ciphertext)?;
        let tx = Transport {
            send,
            recv,
            handshake_hash,
        };
        Ok((tx, payload))
    }
}
pub mod noise_lib {
    // Import hacspec and all needed definitions.

    use super::*;
    use noise_crypto::*;

    /// This module defines the generic Noise processing rules
    /// Section 5: https://noiseprotocol.org/noise.html#processing-rules

    pub struct CipherState {
        k: Option<Vec<u8>>,
        n: u64,
    }

    pub struct SymmetricState {
        cs: CipherState,
        ck: Vec<u8>,
        h: Vec<u8>,
    }

    /// 5.1: The CipherState Object

    pub fn initialize_key(key: Option<Vec<u8>>) -> CipherState {
        CipherState { k: key, n: 0u64 }
    }

    pub fn has_key(cs: &CipherState) -> bool {
        cs.k.is_some()
    }

    pub fn set_nonce(cs: CipherState, n: u64) -> CipherState {
        let CipherState { k, n: _ } = cs;
        CipherState { k, n }
    }

    pub fn encrypt_with_ad(
        cs: CipherState,
        ad: &[u8],
        plaintext: &[u8],
    ) -> Result<(CipherState, Vec<u8>), Error> {
        let CipherState { k, n } = cs;
        if n == 0xffffffffffffffffu64 {
            Err(Error::CryptoError)
        } else {
            match k {
                Some(k) => {
                    let cip = encrypt(&k, n, ad, plaintext);
                    Ok((
                        CipherState {
                            k: Some(k),
                            n: n + 1,
                        },
                        cip,
                    ))
                }
                None => Ok((CipherState { k, n }, plaintext.to_vec())),
            }
        }
    }

    pub fn decrypt_with_ad(
        cs: CipherState,
        ad: &[u8],
        ciphertext: &[u8],
    ) -> Result<(CipherState, Vec<u8>), Error> {
        let CipherState { k, n } = cs;
        if n == 0xffffffffffffffffu64 {
            Err(Error::CryptoError)
        } else {
            match k {
                Some(k) => {
                    let plain = decrypt(&k, n, ad, ciphertext)?;
                    Ok((
                        CipherState {
                            k: Some(k),
                            n: n + 1,
                        },
                        plain,
                    ))
                }
                None => Ok((CipherState { k, n }, ciphertext.to_vec())),
            }
        }
    }

    pub fn rekey(cs: CipherState) -> Result<CipherState, Error> {
        let CipherState { k, n } = cs;
        match k {
            Some(k) => {
                let new_k = noise_crypto::rekey(&k);
                Ok(CipherState { k: Some(new_k), n })
            }
            None => Err(Error::CryptoError),
        }
    }

    /// 5.2: The SymmetricState Object

    pub fn initialize_symmetric(protocol_name: &[u8]) -> SymmetricState {
        let pnlen = protocol_name.len();
        let hv: Vec<u8> = if pnlen < HASHLEN {
            [protocol_name, &vec![0u8; 32 - pnlen]].concat()
        } else {
            hash(protocol_name)
        };
        let ck = hv.clone();
        SymmetricState {
            cs: initialize_key(None),
            ck,
            h: hv,
        }
    }

    pub fn mix_key(st: SymmetricState, input_key_material: &[u8]) -> SymmetricState {
        let SymmetricState { cs: _, ck, h } = st;
        let (ck, mut temp_k) = hkdf2(&ck, input_key_material);
        if HASHLEN == 64 {
            temp_k.truncate(32);
        }
        SymmetricState {
            cs: initialize_key(Some(temp_k)),
            ck,
            h,
        }
    }

    pub fn mix_hash(st: SymmetricState, data: &[u8]) -> SymmetricState {
        let SymmetricState { cs, ck, h } = st;
        SymmetricState {
            cs,
            ck,
            h: hash(&[&h, data].concat()),
        }
    }

    pub fn mix_key_and_hash(st: SymmetricState, input_key_material: &[u8]) -> SymmetricState {
        let SymmetricState { cs: _, ck, h } = st;
        let (ck, temp_h, mut temp_k) = hkdf3(&ck, input_key_material);
        let mut new_h = h;
        new_h.extend_from_slice(&temp_h);
        let new_h = hash(&new_h);
        if HASHLEN == 64 {
            temp_k.truncate(32);
        }
        SymmetricState {
            cs: initialize_key(Some(temp_k)),
            ck,
            h: new_h,
        }
    }

    /// Unclear if we need a special function for psk or we can reuse mix_key_and_hash above
    //pub fn mix_psk(st:SymmetricState,psk:&[u8]) -> (Vec<u8>,Vec<u8>,Vec<u8>) {
    //    let (ck,temp_hash,cs_k) = kdf3(key,psk);
    //    let next_hash = mix_hash(prev_hash,&temp_hash);
    //    (ck,cs_k,next_hash)
    //}

    pub fn encrypt_and_hash(
        st: SymmetricState,
        plaintext: &[u8],
    ) -> Result<(SymmetricState, Vec<u8>), Error> {
        let (new_cs, ciphertext) = encrypt_with_ad(st.cs, &st.h, plaintext)?;
        let mut new_h = st.h.clone();
        new_h.extend_from_slice(&ciphertext);
        let new_h = hash(&new_h);
        Ok((
            SymmetricState {
                cs: new_cs,
                ck: st.ck,
                h: new_h,
            },
            ciphertext,
        ))
    }

    pub fn decrypt_and_hash(
        st: SymmetricState,
        ciphertext: &[u8],
    ) -> Result<(SymmetricState, Vec<u8>), Error> {
        let (new_cs, plaintext) = decrypt_with_ad(st.cs, &st.h, ciphertext)?;
        let mut new_h = st.h.clone();
        new_h.extend_from_slice(ciphertext);
        let new_h = hash(&new_h);
        Ok((
            SymmetricState {
                cs: new_cs,
                ck: st.ck,
                h: new_h,
            },
            plaintext,
        ))
    }

    pub fn split(st: SymmetricState) -> (CipherState, CipherState, Vec<u8>) {
        let (mut temp_k1, mut temp_k2) = hkdf2(&st.ck, &Vec::new());
        if HASHLEN == 64 {
            temp_k1.truncate(32);
            temp_k2.truncate(32);
        }
        (
            initialize_key(Some(temp_k1)),
            initialize_key(Some(temp_k2)),
            st.h,
        )
    }
}
