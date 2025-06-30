module Spec_Sha256

open Core

open FStar.Mul

open FStar.Seq

let v_BLOCK_SIZE:usize = mk_usize 64

let v_LEN_SIZE:usize = mk_usize 8

let v_K_SIZE:usize = mk_usize 64

let v_HASH_SIZE:usize = mk_usize (256 / 8)

type t_Block = t_Array u8 v_BLOCK_SIZE

type t_OpTableType = t_Array u8 (mk_usize 12)

type t_Sha256Digest = t_Array u8 v_HASH_SIZE

type t_RoundConstantsTable = t_Array u32 v_K_SIZE

type t_Hash = t_Array u32 v_LEN_SIZE

let v_K_TABLE:t_RoundConstantsTable =
  let list =
    [
      mk_u32 1116352408; mk_u32 1899447441; mk_u32 3049323471; mk_u32 3921009573; mk_u32 961987163;
      mk_u32 1508970993; mk_u32 2453635748; mk_u32 2870763221; mk_u32 3624381080; mk_u32 310598401;
      mk_u32 607225278; mk_u32 1426881987; mk_u32 1925078388; mk_u32 2162078206; mk_u32 2614888103;
      mk_u32 3248222580; mk_u32 3835390401; mk_u32 4022224774; mk_u32 264347078; mk_u32 604807628;
      mk_u32 770255983; mk_u32 1249150122; mk_u32 1555081692; mk_u32 1996064986; mk_u32 2554220882;
      mk_u32 2821834349; mk_u32 2952996808; mk_u32 3210313671; mk_u32 3336571891; mk_u32 3584528711;
      mk_u32 113926993; mk_u32 338241895; mk_u32 666307205; mk_u32 773529912; mk_u32 1294757372;
      mk_u32 1396182291; mk_u32 1695183700; mk_u32 1986661051; mk_u32 2177026350; mk_u32 2456956037;
      mk_u32 2730485921; mk_u32 2820302411; mk_u32 3259730800; mk_u32 3345764771; mk_u32 3516065817;
      mk_u32 3600352804; mk_u32 4094571909; mk_u32 275423344; mk_u32 430227734; mk_u32 506948616;
      mk_u32 659060556; mk_u32 883997877; mk_u32 958139571; mk_u32 1322822218; mk_u32 1537002063;
      mk_u32 1747873779; mk_u32 1955562222; mk_u32 2024104815; mk_u32 2227730452; mk_u32 2361852424;
      mk_u32 2428436474; mk_u32 2756734187; mk_u32 3204031479; mk_u32 3329325298
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 64);
  Rust_primitives.Hax.array_of_list 64 list

let v_HASH_INIT:t_Hash =
  let list =
    [
      mk_u32 1779033703;
      mk_u32 3144134277;
      mk_u32 1013904242;
      mk_u32 2773480762;
      mk_u32 1359893119;
      mk_u32 2600822924;
      mk_u32 528734635;
      mk_u32 1541459225
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
  Rust_primitives.Hax.array_of_list 8 list
  
// Helper functions for working with u32

let from_be_bytes (bytes: t_Array u8 (mk_usize 4)) : u32 =
  let b0: u32 = cast (Seq.index bytes 0) <: u32 in
  let b1: u32 = cast (Seq.index bytes 1) <: u32 in
  let b2: u32 = cast (Seq.index bytes 2) <: u32 in
  let b3: u32 = cast (Seq.index bytes 3) <: u32 in
  (b0 <<! (mk_u32 24)) +. (b1 <<! (mk_u32 16)) +. (b2 <<! (mk_u32 8)) +. b3


// FIPS PUB 180-4, Section 2.2.2

#set-options "--query_stats"

let f_ROTR (n: u32) (x: u32) = Core.Num.impl_u32__rotate_right x n
// let f_ROTR (n: u32{mk_u32 0 <. n && n <. mk_u32 32}) (x: u32) :  u32  =
//   (x >>! n) |. (x <<! (mk_u32 32 -! n))

let f_SHR (n: u32{v n < bits U32}) (x: u32) = shift_right x n

// let test_f_shift_left () =
//   let x: u32 = mk_u32 8 in
//   let n: u32 = mk_u32 2 in
//   let result: u32 = shift_left x n in
//   assert (v result = 32)
// 
// let test_f_ROTR_1 () = 
//   let x: u32 = mk_u32 8 in
//   let n: u32 = mk_u32 2 in
//   let result: u32 = f_ROTR n x in
//   assert (v result = 3)

// FIPS PUB 180-4, Section 4.1.2

// TODO: Xor associativity with 3 arguments

let f_ch (x y z: u32) : u32 = (x &. y) ^. ((~.x) &. z)

let f_maj (x y z: u32) : u32 = (x &. y) ^. (x &. z) ^. (y &. z)

let f_SIGMA_0 x : u32 = ((f_ROTR (mk_u32 2) x) ^. (f_ROTR (mk_u32 13) x)) ^. (f_ROTR (mk_u32 22) x)

let f_SIGMA_1 x : u32 = ((f_ROTR (mk_u32 6) x) ^. (f_ROTR (mk_u32 11) x)) ^. (f_ROTR (mk_u32 25) x) 

let f_sigma_0 x : u32 = ((f_ROTR (mk_u32 7) x) ^. (f_ROTR (mk_u32 18) x)) ^. (f_SHR (mk_u32 3) x) 

let f_sigma_1 x : u32 = ((f_ROTR (mk_u32 17) x) ^. (f_ROTR (mk_u32 19) x)) ^. (f_SHR (mk_u32 10) x) 
 
let f_sigma (x: u32) (i: usize{i <. mk_usize 4}) : u32 =
  match v i with
  | 0 -> f_SIGMA_0 x
  | 1 -> f_SIGMA_1 x
  | 2 -> f_sigma_0 x
  | 3 -> f_sigma_1 x

// FIPS PUB 180-4, Section 5.2.1

let f_parse_message_block_i (block: t_Block) (i: usize{i <. mk_usize 16}) (out: t_Array u32 (mk_usize 16)) : t_Array u32 (mk_usize 16) =
  let b0 = Seq.index block (4 * v i) in
  let b1 = Seq.index block (4 * v i + 1) in
  let b2 = Seq.index block (4 * v i + 2) in
  let b3 = Seq.index block (4 * v i + 3) in
  let list = [b0; b1; b2; b3] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
  let word = Core.Num.impl_u32__from_be_bytes (Rust_primitives.Arrays.of_list #u8 list) in
  Seq.upd out (v i) word

let rec f_parse_message_block_n (block: t_Block) (out: t_Array u32 (mk_usize 16)) (n: usize{v n <= 16}) (i: usize{v i <= v n}) 
  : Tot (t_Array u32 (mk_usize 16)) (decreases (16 - v i)) =
  if v i = v n then
    out
  else
    let out' = f_parse_message_block_i block i out in
    f_parse_message_block_n block out' n (i +! mk_usize 1)

let f_parse_message_block (block: t_Block) : t_Array u32 (mk_usize 16) =
  let w_init = Rust_primitives.Hax.repeat (mk_u32 0) (mk_usize 16) in
  f_parse_message_block_n block w_init (mk_usize 16) (mk_usize 0)



// FIBS PUB 180-4, Section 6.2.2, Step 1

let rec f_schedule_word (block: t_Block) (t: nat{t < 64}) : Tot u32 (decreases t) =
  if t < 16
  then
    let b = f_parse_message_block block in
    Seq.index b t
  else
    let w16 = f_schedule_word block (t - 16) in
    let w15 = f_schedule_word block (t - 15) in
    let w7 = f_schedule_word block (t - 7) in
    let w2 = f_schedule_word block (t - 2) in
    let s1 = f_sigma_1 w2 in
    let s0 = f_sigma_0 w15 in
    s1 +. w7 +. s0 +. w16

let f_schedule (block: t_Block) : t_RoundConstantsTable =
  createi (mk_usize 64) (fun i -> f_schedule_word block (v i))



// FIPS PUB 180-4, Section 6.2.2, Step 2, 3 and 4

let f_shuffle_i (ws: t_RoundConstantsTable) (hashi: t_Hash) (i: usize{i <. v_K_SIZE}): t_Hash =
  let a = Seq.index hashi 0 in
  let b = Seq.index hashi 1 in
  let c = Seq.index hashi 2 in
  let d = Seq.index hashi 3 in
  let e = Seq.index hashi 4 in
  let f = Seq.index hashi 5 in
  let g = Seq.index hashi 6 in
  let h = Seq.index hashi 7 in
  let t1 = h +. (f_SIGMA_1 e) +. (f_ch e f g) +. v_K_TABLE.[ i ] +. ws.[ i ] in
  let t2 = (f_SIGMA_0 a) +. (f_maj a b c) in
  let hashi = Seq.upd hashi 0 (t1 +. t2) in
  let hashi = Seq.upd hashi 1 a in
  let hashi = Seq.upd hashi 2 b in
  let hashi = Seq.upd hashi 3 c in
  let hashi = Seq.upd hashi 4 (d +. t1) in
  let hashi = Seq.upd hashi 5 e in
  let hashi = Seq.upd hashi 6 f in
  let hashi = Seq.upd hashi 7 g in
  hashi

let rec f_shuffle_rec (ws: t_RoundConstantsTable) (hashi: t_Hash) (i: usize{i <=. v_K_SIZE})
: Tot t_Hash (decreases v v_K_SIZE - v i) =
  if i =. v_K_SIZE then
    hashi
  else 
    f_shuffle_rec ws (f_shuffle_i ws hashi i) (i +! (mk_usize 1))

let f_shuffle (ws: t_RoundConstantsTable) (hashi: t_Hash) : t_Hash =
  f_shuffle_rec ws hashi (mk_usize 0)
  

// FIPS PUB 180-4, Section 6.2.2, Iterations

let f_compress (block: t_Block) (h_in: t_Hash) : t_Hash =
  let s = f_schedule block in
  let h = f_shuffle s h_in in
  Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
    v_LEN_SIZE
    (fun _ _ -> true)
    h
    (fun (h: t_Hash) i -> Seq.upd h (v i) (h.[ i ] +. h_in.[ i ]))


// FIPS PUB 180-4, Section 6.2.2, Last Step

let f_hash_to_digest (hash: t_Hash) : t_Sha256Digest =
  createi v_HASH_SIZE
    (fun i ->
        let word_index = v i / 4 in
        let byte_index = v i % 4 in
        let word = hash.[ mk_usize word_index ] in
        let word_bytes = Core.Num.impl_u32__to_be_bytes word in
        word_bytes.[ mk_usize byte_index ])


// FIPS PUB 180-4, Section 6.2.2, Main Hash Function

#set-options "--split_queries always"

let hash (msg: t_Slice u8) : t_Sha256Digest =
  let h:t_Hash = v_HASH_INIT in
  let bit_len:usize = Rust_primitives.Arrays.length msg *. v_LEN_SIZE in
  let _msg_len = Rust_primitives.Arrays.length msg in
  let full_block_len = _msg_len -! (_msg_len %! v_BLOCK_SIZE) in

  // Compress all full blocks
  let h =
    Rust_primitives.Hax.Folds.fold_chunked_slice v_BLOCK_SIZE
      (Rust_primitives.Arrays.slice msg (mk_usize 0) full_block_len)
      (fun _ _ -> true)
      h
      (fun (h: t_Hash) block -> f_compress block h)
  in
  
  // Get the remainder of the message
  let _rem = Rust_primitives.Arrays.slice msg full_block_len _msg_len in
  let _rem_len = _msg_len -! full_block_len in
  
  // Calculate padding parameters
  let total_len = _rem_len +! (mk_usize 1) in  // + 1 for the 0x80 byte
  let pad_start = 
    if total_len +! v_LEN_SIZE >. v_BLOCK_SIZE then
      (v_BLOCK_SIZE *. (mk_usize 2)) -! v_LEN_SIZE  // BLOCK_SIZE * 2 - LEN_SIZE
    else
      v_BLOCK_SIZE -! v_LEN_SIZE  // BLOCK_SIZE - LEN_SIZE
  in
  
  // Convert bit_len to big-endian bytes
  let len_bytes = Core.Num.impl_u64__to_be_bytes (cast bit_len <: u64) in
  
  // Create final_blocks array (128 bytes = 2 * BLOCK_SIZE) with padding logic
  let final_blocks = Rust_primitives.Arrays.createi (v_BLOCK_SIZE *. (mk_usize 2)) (fun i ->
    if i <. _rem_len then
      // Copy remainder bytes
      Seq.index _rem (v i)
    else if i =. _rem_len then
      // Add the 0x80 byte
      mk_u8 0x80
    else if i >=. pad_start && i <. (pad_start +! v_LEN_SIZE) then
      // Set length bytes at the end of the last block
      Seq.index len_bytes (v (i -! pad_start))
    else
      // Zero padding
      mk_u8 0
  ) in

  // Determine how many final blocks to process
  let final_len = 
    if pad_start =. (v_BLOCK_SIZE -! v_LEN_SIZE) then
      v_BLOCK_SIZE  // One block
    else
      v_BLOCK_SIZE *. (mk_usize 2)  // Two blocks
  in
  
  // Process the final block(s)
  let h = Rust_primitives.Hax.Folds.fold_chunked_slice v_BLOCK_SIZE 
    (Rust_primitives.Arrays.slice final_blocks (mk_usize 0) final_len)
    (fun _ _ -> true)
    h
    (fun (h: t_Hash) block -> f_compress block h)
  in
  
  f_hash_to_digest h

let sha256 msg = hash msg


// Tests 
  
// #set-options "--z3rlimit 2500 --query_stats"

// let test_from_be_bytes_1 () =
//   let bytes: t_Array u8 (mk_usize 4) = Rust_primitives.Hax.array_of_list 4 
//   [ 
//     mk_u8 0; 
//     mk_u8 0; 
//     mk_u8 0; 
//     mk_u8 42
//   ] 
//   in
//   let result: u32 = from_be_bytes bytes in
//   assert (v result = 42)
// 
// let test_from_be_bytes_2 () =
//   let bytes: t_Array u8 (mk_usize 4) = Rust_primitives.Hax.array_of_list 4 
//   [ 
//     mk_u8 0; 
//     mk_u8 0;
//     mk_u8 86;
//     mk_u8 120
//   ] 
//   in
//   let result: u32 = from_be_bytes bytes in
//   assert (v result = 22136)
// 
// let test_from_be_bytes_3 () =
//   let bytes: t_Array u8 (mk_usize 4) = Rust_primitives.Hax.array_of_list 4
//   [ 
//     mk_u8 0;
//     mk_u8 167;
//     mk_u8 86;
//     mk_u8 120
//   ] 
//   in
//   let result: u32 = from_be_bytes bytes in
//   assert (v result = 10966648)
// 
// let test_from_be_bytes_4 () =
//   let bytes: t_Array u8 (mk_usize 4) = Rust_primitives.Hax.array_of_list 4
//   [
//     mk_u8 214;
//     mk_u8 167;
//     mk_u8 86;
//     mk_u8 120
//   ] 
//   in
//   let result: u32 = from_be_bytes bytes in
//   assert (v result = 3601290872)
// 
// let test_parse_message_block () =
//   let block: t_Block = 
//     let list = [
//       mk_u8 0; mk_u8 0; mk_u8 0; mk_u8 42;
//       mk_u8 0; mk_u8 0; mk_u8 86; mk_u8 120;
//       mk_u8 0; mk_u8 167; mk_u8 86; mk_u8 120;
//       mk_u8 214; mk_u8 167; mk_u8 86; mk_u8 120;
//       mk_u8 0; mk_u8 0; mk_u8 0; mk_u8 0;
//       mk_u8 0; mk_u8 0; mk_u8 0; mk_u8 0;
//       mk_u8 0; mk_u8 0; mk_u8 0; mk_u8 0;
//       mk_u8 0; mk_u8 0; mk_u8 0; mk_u8 0;
//       mk_u8 0; mk_u8 0; mk_u8 0; mk_u8 0;
//       mk_u8 0; mk_u8 0; mk_u8 0; mk_u8 0;
//       mk_u8 0; mk_u8 0; mk_u8 0; mk_u8 0;
//       mk_u8 0; mk_u8 0; mk_u8 0; mk_u8 0;
//       mk_u8 0; mk_u8 0; mk_u8 0; mk_u8 0;
//       mk_u8 0; mk_u8 0; mk_u8 0; mk_u8 0;
//       mk_u8 0; mk_u8 0; mk_u8 0; mk_u8 0;
//       mk_u8 0; mk_u8 0; mk_u8 0; mk_u8 0;
//       mk_u8 0; mk_u8 0; mk_u8 0; mk_u8 0;
//       mk_u8 0; mk_u8 0; mk_u8 0; mk_u8 0;
//       mk_u8 0; mk_u8 0; mk_u8 0; mk_u8 0;
//     ] in 
//   FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) (v v_BLOCK_SIZE));
//   Rust_primitives.Hax.array_of_list (v v_BLOCK_SIZE) list in
//   let parsed = f_parse_message_block block in
//   let result1: u32 = Seq.index parsed 0 in
//   let result2: u32 = Seq.index parsed 1 in
//   let result3: u32 = Seq.index parsed 2 in
//   let result4: u32 = Seq.index parsed 3 in
//   assert (v result1 = 42)
