module Tests.Legacy__proverif_noise__lib.Noise_lib
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

/// This module defines the generic Noise processing rules
/// Section 5: https://noiseprotocol.org/noise.html#processing-rules
type t_CipherState = {
  f_k:Core.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global);
  f_n:u64
}

type t_SymmetricState = {
  f_cs:t_CipherState;
  f_ck:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global;
  f_h:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global
}

/// 5.1: The CipherState Object
let initialize_key (key: Core.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
    : t_CipherState = { f_k = key; f_n = mk_u64 0 } <: t_CipherState

let has_key (cs: t_CipherState) : bool =
  Core.Option.impl__is_some #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) cs.f_k

/// @fail(extraction): ssprove(HAX0001)
let set_nonce (cs: t_CipherState) (n: u64) : t_CipherState =
  let { f_k = k ; f_n = _ }:t_CipherState = cs in
  { f_k = k; f_n = n } <: t_CipherState

/// @fail(extraction): ssprove(HAX0001)
let encrypt_with_ad (cs: t_CipherState) (ad plaintext: t_Slice u8)
    : Core.Result.t_Result (t_CipherState & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error =
  let { f_k = k ; f_n = n }:t_CipherState = cs in
  if n =. mk_u64 18446744073709551615
  then
    Core.Result.Result_Err
    (Tests.Legacy__proverif_noise__lib.Noise_crypto.Error_CryptoError
      <:
      Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error)
    <:
    Core.Result.t_Result (t_CipherState & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error
  else
    match k <: Core.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) with
    | Core.Option.Option_Some k ->
      let cip:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
        Tests.Legacy__proverif_noise__lib.Noise_crypto.encrypt (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec
                  u8 Alloc.Alloc.t_Global)
              #FStar.Tactics.Typeclasses.solve
              k
            <:
            t_Slice u8)
          n
          ad
          plaintext
      in
      Core.Result.Result_Ok
      (({
            f_k
            =
            Core.Option.Option_Some k
            <:
            Core.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global);
            f_n = n +! mk_u64 1
          }
          <:
          t_CipherState),
        cip
        <:
        (t_CipherState & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
      <:
      Core.Result.t_Result (t_CipherState & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
        Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error
    | Core.Option.Option_None  ->
      Core.Result.Result_Ok
      (({ f_k = k; f_n = n } <: t_CipherState), Alloc.Slice.impl__to_vec #u8 plaintext
        <:
        (t_CipherState & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
      <:
      Core.Result.t_Result (t_CipherState & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
        Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error

/// @fail(extraction): ssprove(HAX0001)
let decrypt_with_ad (cs: t_CipherState) (ad ciphertext: t_Slice u8)
    : Core.Result.t_Result (t_CipherState & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error =
  let { f_k = k ; f_n = n }:t_CipherState = cs in
  if n =. mk_u64 18446744073709551615
  then
    Core.Result.Result_Err
    (Tests.Legacy__proverif_noise__lib.Noise_crypto.Error_CryptoError
      <:
      Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error)
    <:
    Core.Result.t_Result (t_CipherState & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error
  else
    match k <: Core.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) with
    | Core.Option.Option_Some k ->
      (match
          Tests.Legacy__proverif_noise__lib.Noise_crypto.decrypt (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec
                    u8 Alloc.Alloc.t_Global)
                #FStar.Tactics.Typeclasses.solve
                k
              <:
              t_Slice u8)
            n
            ad
            ciphertext
          <:
          Core.Result.t_Result (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
            Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error
        with
        | Core.Result.Result_Ok plain ->
          Core.Result.Result_Ok
          (({
                f_k
                =
                Core.Option.Option_Some k
                <:
                Core.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global);
                f_n = n +! mk_u64 1
              }
              <:
              t_CipherState),
            plain
            <:
            (t_CipherState & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
          <:
          Core.Result.t_Result (t_CipherState & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
            Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error
        | Core.Result.Result_Err err ->
          Core.Result.Result_Err err
          <:
          Core.Result.t_Result (t_CipherState & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
            Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error)
    | Core.Option.Option_None  ->
      Core.Result.Result_Ok
      (({ f_k = k; f_n = n } <: t_CipherState), Alloc.Slice.impl__to_vec #u8 ciphertext
        <:
        (t_CipherState & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
      <:
      Core.Result.t_Result (t_CipherState & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
        Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error

/// @fail(extraction): ssprove(HAX0001)
let rekey (cs: t_CipherState)
    : Core.Result.t_Result t_CipherState Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error =
  let { f_k = k ; f_n = n }:t_CipherState = cs in
  match k <: Core.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) with
  | Core.Option.Option_Some k ->
    let new_k:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
      Tests.Legacy__proverif_noise__lib.Noise_crypto.rekey (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec
                u8 Alloc.Alloc.t_Global)
            #FStar.Tactics.Typeclasses.solve
            k
          <:
          t_Slice u8)
    in
    Core.Result.Result_Ok
    ({
        f_k
        =
        Core.Option.Option_Some new_k
        <:
        Core.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global);
        f_n = n
      }
      <:
      t_CipherState)
    <:
    Core.Result.t_Result t_CipherState Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error
  | Core.Option.Option_None  ->
    Core.Result.Result_Err
    (Tests.Legacy__proverif_noise__lib.Noise_crypto.Error_CryptoError
      <:
      Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error)
    <:
    Core.Result.t_Result t_CipherState Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error

/// 5.2: The SymmetricState Object
let initialize_symmetric (protocol_name: t_Slice u8) : t_SymmetricState =
  let pnlen:usize = Core.Slice.impl__len #u8 protocol_name in
  let (hv: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global):Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    if pnlen <. Tests.Legacy__proverif_noise__lib.Noise_crypto.v_HASHLEN
    then
      Alloc.Slice.impl__concat #(t_Slice u8)
        #u8
        ((let list =
              [
                protocol_name;
                Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                  #FStar.Tactics.Typeclasses.solve
                  (Alloc.Vec.from_elem #u8 (mk_u8 0) (mk_usize 32 -! pnlen <: usize)
                    <:
                    Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
              ]
            in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
            Rust_primitives.Hax.array_of_list 2 list)
          <:
          t_Slice (t_Slice u8))
    else Tests.Legacy__proverif_noise__lib.Noise_crypto.hash protocol_name
  in
  let ck:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Core.Clone.f_clone #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      #FStar.Tactics.Typeclasses.solve
      hv
  in
  {
    f_cs
    =
    initialize_key (Core.Option.Option_None
        <:
        Core.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global));
    f_ck = ck;
    f_h = hv
  }
  <:
  t_SymmetricState

/// @fail(extraction): ssprove(HAX0001)
let mix_key (st: t_SymmetricState) (input_key_material: t_Slice u8) : t_SymmetricState =
  let { f_cs = _ ; f_ck = ck ; f_h = h }:t_SymmetricState = st in
  let ck, temp_k:(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  =
    Tests.Legacy__proverif_noise__lib.Noise_crypto.hkdf2 (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec
              u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          ck
        <:
        t_Slice u8)
      input_key_material
  in
  let temp_k:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    if Tests.Legacy__proverif_noise__lib.Noise_crypto.v_HASHLEN =. mk_usize 64
    then
      let temp_k:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
        Alloc.Vec.impl_1__truncate #u8 #Alloc.Alloc.t_Global temp_k (mk_usize 32)
      in
      temp_k
    else temp_k
  in
  {
    f_cs
    =
    initialize_key (Core.Option.Option_Some temp_k
        <:
        Core.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global));
    f_ck = ck;
    f_h = h
  }
  <:
  t_SymmetricState

/// @fail(extraction): ssprove(HAX0001)
let mix_hash (st: t_SymmetricState) (data: t_Slice u8) : t_SymmetricState =
  let { f_cs = cs ; f_ck = ck ; f_h = h }:t_SymmetricState = st in
  {
    f_cs = cs;
    f_ck = ck;
    f_h
    =
    Tests.Legacy__proverif_noise__lib.Noise_crypto.hash (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8
              Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          (Alloc.Slice.impl__concat #(t_Slice u8)
              #u8
              ((let list =
                    [
                      Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
                        #FStar.Tactics.Typeclasses.solve
                        h;
                      data
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
  }
  <:
  t_SymmetricState

/// @fail(extraction): ssprove(HAX0001)
let mix_key_and_hash (st: t_SymmetricState) (input_key_material: t_Slice u8) : t_SymmetricState =
  let { f_cs = _ ; f_ck = ck ; f_h = h }:t_SymmetricState = st in
  let ck, temp_h, temp_k:(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global &
    Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global &
    Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) =
    Tests.Legacy__proverif_noise__lib.Noise_crypto.hkdf3 (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec
              u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          ck
        <:
        t_Slice u8)
      input_key_material
  in
  let new_h:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = h in
  let new_h:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Alloc.Vec.impl_2__extend_from_slice #u8
      #Alloc.Alloc.t_Global
      new_h
      (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          temp_h
        <:
        t_Slice u8)
  in
  let new_h:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Tests.Legacy__proverif_noise__lib.Noise_crypto.hash (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8
              Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          new_h
        <:
        t_Slice u8)
  in
  let temp_k:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    if Tests.Legacy__proverif_noise__lib.Noise_crypto.v_HASHLEN =. mk_usize 64
    then
      let temp_k:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
        Alloc.Vec.impl_1__truncate #u8 #Alloc.Alloc.t_Global temp_k (mk_usize 32)
      in
      temp_k
    else temp_k
  in
  {
    f_cs
    =
    initialize_key (Core.Option.Option_Some temp_k
        <:
        Core.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global));
    f_ck = ck;
    f_h = new_h
  }
  <:
  t_SymmetricState

/// Unclear if we need a special function for psk or we can reuse mix_key_and_hash above
let encrypt_and_hash (st: t_SymmetricState) (plaintext: t_Slice u8)
    : Core.Result.t_Result (t_SymmetricState & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error =
  match
    encrypt_with_ad st.f_cs
      (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          st.f_h
        <:
        t_Slice u8)
      plaintext
    <:
    Core.Result.t_Result (t_CipherState & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error
  with
  | Core.Result.Result_Ok (new_cs, ciphertext) ->
    let new_h:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
      Core.Clone.f_clone #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
        #FStar.Tactics.Typeclasses.solve
        st.f_h
    in
    let new_h:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
      Alloc.Vec.impl_2__extend_from_slice #u8
        #Alloc.Alloc.t_Global
        new_h
        (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
            #FStar.Tactics.Typeclasses.solve
            ciphertext
          <:
          t_Slice u8)
    in
    let new_h:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
      Tests.Legacy__proverif_noise__lib.Noise_crypto.hash (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec
                u8 Alloc.Alloc.t_Global)
            #FStar.Tactics.Typeclasses.solve
            new_h
          <:
          t_Slice u8)
    in
    Core.Result.Result_Ok
    (({ f_cs = new_cs; f_ck = st.f_ck; f_h = new_h } <: t_SymmetricState), ciphertext
      <:
      (t_SymmetricState & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
    <:
    Core.Result.t_Result (t_SymmetricState & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result (t_SymmetricState & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error

let decrypt_and_hash (st: t_SymmetricState) (ciphertext: t_Slice u8)
    : Core.Result.t_Result (t_SymmetricState & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error =
  match
    decrypt_with_ad st.f_cs
      (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          st.f_h
        <:
        t_Slice u8)
      ciphertext
    <:
    Core.Result.t_Result (t_CipherState & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error
  with
  | Core.Result.Result_Ok (new_cs, plaintext) ->
    let new_h:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
      Core.Clone.f_clone #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
        #FStar.Tactics.Typeclasses.solve
        st.f_h
    in
    let new_h:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
      Alloc.Vec.impl_2__extend_from_slice #u8 #Alloc.Alloc.t_Global new_h ciphertext
    in
    let new_h:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
      Tests.Legacy__proverif_noise__lib.Noise_crypto.hash (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec
                u8 Alloc.Alloc.t_Global)
            #FStar.Tactics.Typeclasses.solve
            new_h
          <:
          t_Slice u8)
    in
    Core.Result.Result_Ok
    (({ f_cs = new_cs; f_ck = st.f_ck; f_h = new_h } <: t_SymmetricState), plaintext
      <:
      (t_SymmetricState & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global))
    <:
    Core.Result.t_Result (t_SymmetricState & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error
  | Core.Result.Result_Err err ->
    Core.Result.Result_Err err
    <:
    Core.Result.t_Result (t_SymmetricState & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      Tests.Legacy__proverif_noise__lib.Noise_crypto.t_Error

let split (st: t_SymmetricState)
    : (t_CipherState & t_CipherState & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) =
  let temp_k1, temp_k2:(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global &
    Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) =
    Tests.Legacy__proverif_noise__lib.Noise_crypto.hkdf2 (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec
              u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          st.f_ck
        <:
        t_Slice u8)
      (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          (Alloc.Vec.impl__new #u8 () <: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
        <:
        t_Slice u8)
  in
  let temp_k1, temp_k2:(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global &
    Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) =
    if Tests.Legacy__proverif_noise__lib.Noise_crypto.v_HASHLEN =. mk_usize 64
    then
      let temp_k1:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
        Alloc.Vec.impl_1__truncate #u8 #Alloc.Alloc.t_Global temp_k1 (mk_usize 32)
      in
      let temp_k2:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
        Alloc.Vec.impl_1__truncate #u8 #Alloc.Alloc.t_Global temp_k2 (mk_usize 32)
      in
      temp_k1, temp_k2
      <:
      (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
    else
      temp_k1, temp_k2
      <:
      (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
  in
  initialize_key (Core.Option.Option_Some temp_k1
      <:
      Core.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)),
  initialize_key (Core.Option.Option_Some temp_k2
      <:
      Core.Option.t_Option (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)),
  st.f_h
  <:
  (t_CipherState & t_CipherState & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
