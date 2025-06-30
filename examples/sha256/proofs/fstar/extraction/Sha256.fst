module Sha256
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_BLOCK_SIZE: usize = mk_usize 64

let v_LEN_SIZE: usize = mk_usize 8

let v_K_SIZE: usize = mk_usize 64

let v_HASH_SIZE: usize = mk_usize 256 /! mk_usize 8

let ch (x y z: u32) : u32 = (x &. y <: u32) ^. ((~.x <: u32) &. z <: u32)

let maj (x y z: u32) : u32 = (x &. y <: u32) ^. ((x &. z <: u32) ^. (y &. z <: u32) <: u32)

let v_OP_TABLE: t_Array u8 (mk_usize 12) =
  let list =
    [
      mk_u8 2; mk_u8 13; mk_u8 22; mk_u8 6; mk_u8 11; mk_u8 25; mk_u8 7; mk_u8 18; mk_u8 3; mk_u8 17;
      mk_u8 19; mk_u8 10
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 12);
  Rust_primitives.Hax.array_of_list 12 list

let v_K_TABLE: t_Array u32 (mk_usize 64) =
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

let v_HASH_INIT: t_Array u32 (mk_usize 8) =
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

let sigma (x: u32) (i op: usize) : Prims.Pure u32 (requires i <. mk_usize 4) (fun _ -> Prims.l_True) =
  let (tmp: u32):u32 =
    Core.Num.impl_u32__rotate_right x
      (Core.Convert.f_into #u8
          #u32
          #FStar.Tactics.Typeclasses.solve
          (v_OP_TABLE.[ (mk_usize 3 *! i <: usize) +! mk_usize 2 <: usize ] <: u8)
        <:
        u32)
  in
  let tmp:u32 =
    if op =. mk_usize 0
    then x >>! (v_OP_TABLE.[ (mk_usize 3 *! i <: usize) +! mk_usize 2 <: usize ] <: u8)
    else tmp
  in
  let rot_val_1_:u32 =
    Core.Convert.f_into #u8
      #u32
      #FStar.Tactics.Typeclasses.solve
      (v_OP_TABLE.[ mk_usize 3 *! i <: usize ] <: u8)
  in
  let rot_val_2_:u32 =
    Core.Convert.f_into #u8
      #u32
      #FStar.Tactics.Typeclasses.solve
      (v_OP_TABLE.[ (mk_usize 3 *! i <: usize) +! mk_usize 1 <: usize ] <: u8)
  in
  ((Core.Num.impl_u32__rotate_right x rot_val_1_ <: u32) ^.
    (Core.Num.impl_u32__rotate_right x rot_val_2_ <: u32)
    <:
    u32) ^.
  tmp

let to_be_u32s (block: t_Array u8 (mk_usize 64))
    : Prims.Pure (t_Array u32 (mk_usize 16))
      Prims.l_True
      (ensures
        fun result ->
          let result:t_Array u32 (mk_usize 16) = result in
          (Core.Slice.impl__len #u32 (result <: t_Slice u32) <: usize) =. mk_usize 16) =
  let out:t_Array u32 (mk_usize 16) = Rust_primitives.Hax.repeat (mk_u32 0) (mk_usize 16) in
  let out:t_Array u32 (mk_usize 16) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 16)
      (fun out temp_1_ ->
          let out:t_Array u32 (mk_usize 16) = out in
          let _:usize = temp_1_ in
          true)
      out
      (fun out i ->
          let out:t_Array u32 (mk_usize 16) = out in
          let i:usize = i in
          let block_chunk_array:u32 =
            Core.Num.impl_u32__from_be_bytes (Core.Result.impl__unwrap #(t_Array u8 (mk_usize 4))
                  #Core.Array.t_TryFromSliceError
                  (Core.Convert.f_try_into #(t_Slice u8)
                      #(t_Array u8 (mk_usize 4))
                      #FStar.Tactics.Typeclasses.solve
                      (block.[ {
                            Core.Ops.Range.f_start = i *! mk_usize 4 <: usize;
                            Core.Ops.Range.f_end = (i +! mk_usize 1 <: usize) *! mk_usize 4 <: usize
                          }
                          <:
                          Core.Ops.Range.t_Range usize ]
                        <:
                        t_Slice u8)
                    <:
                    Core.Result.t_Result (t_Array u8 (mk_usize 4)) Core.Array.t_TryFromSliceError)
                <:
                t_Array u8 (mk_usize 4))
          in
          let out:t_Array u32 (mk_usize 16) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out i block_chunk_array
          in
          out)
  in
  out

let schedule (block: t_Array u8 (mk_usize 64)) : t_Array u32 (mk_usize 64) =
  let b:t_Array u32 (mk_usize 16) = to_be_u32s block in
  let s:t_Array u32 (mk_usize 64) = Rust_primitives.Hax.repeat (mk_u32 0) (mk_usize 64) in
  let s:t_Array u32 (mk_usize 64) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_K_SIZE
      (fun s i ->
          let s:t_Array u32 (mk_usize 64) = s in
          let i:usize = i in
          (Core.Slice.impl__len #u32 (b <: t_Slice u32) <: usize) =. mk_usize 16 <: bool)
      s
      (fun s i ->
          let s:t_Array u32 (mk_usize 64) = s in
          let i:usize = i in
          if i <. mk_usize 16 <: bool
          then
            let s:t_Array u32 (mk_usize 64) =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s i (b.[ i ] <: u32)
            in
            s
          else
            let t16:u32 = s.[ i -! mk_usize 16 <: usize ] in
            let t15:u32 = s.[ i -! mk_usize 15 <: usize ] in
            let t7:u32 = s.[ i -! mk_usize 7 <: usize ] in
            let t2:u32 = s.[ i -! mk_usize 2 <: usize ] in
            let s1:u32 = sigma t2 (mk_usize 3) (mk_usize 0) in
            let s0:u32 = sigma t15 (mk_usize 2) (mk_usize 0) in
            let s:t_Array u32 (mk_usize 64) =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
                i
                (Core.Num.impl_u32__wrapping_add (Core.Num.impl_u32__wrapping_add (Core.Num.impl_u32__wrapping_add
                            s1
                            t7
                          <:
                          u32)
                        s0
                      <:
                      u32)
                    t16
                  <:
                  u32)
            in
            s)
  in
  s

let shuffle (ws: t_Array u32 (mk_usize 64)) (hash: t_Array u32 (mk_usize 8))
    : t_Array u32 (mk_usize 8) =
  let hash:t_Array u32 (mk_usize 8) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_K_SIZE
      (fun hash temp_1_ ->
          let hash:t_Array u32 (mk_usize 8) = hash in
          let _:usize = temp_1_ in
          true)
      hash
      (fun hash i ->
          let hash:t_Array u32 (mk_usize 8) = hash in
          let i:usize = i in
          let a0:u32 = hash.[ mk_usize 0 ] in
          let b0:u32 = hash.[ mk_usize 1 ] in
          let c0:u32 = hash.[ mk_usize 2 ] in
          let d0:u32 = hash.[ mk_usize 3 ] in
          let e0:u32 = hash.[ mk_usize 4 ] in
          let f0:u32 = hash.[ mk_usize 5 ] in
          let g0:u32 = hash.[ mk_usize 6 ] in
          let (h0: u32):u32 = hash.[ mk_usize 7 ] in
          let t1:u32 =
            Core.Num.impl_u32__wrapping_add (Core.Num.impl_u32__wrapping_add (Core.Num.impl_u32__wrapping_add
                      (Core.Num.impl_u32__wrapping_add h0
                          (sigma e0 (mk_usize 1) (mk_usize 1) <: u32)
                        <:
                        u32)
                      (ch e0 f0 g0 <: u32)
                    <:
                    u32)
                  (v_K_TABLE.[ i ] <: u32)
                <:
                u32)
              (ws.[ i ] <: u32)
          in
          let t2:u32 =
            Core.Num.impl_u32__wrapping_add (sigma a0 (mk_usize 0) (mk_usize 1) <: u32)
              (maj a0 b0 c0 <: u32)
          in
          let hash:t_Array u32 (mk_usize 8) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize hash
              (mk_usize 0)
              (Core.Num.impl_u32__wrapping_add t1 t2 <: u32)
          in
          let hash:t_Array u32 (mk_usize 8) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize hash (mk_usize 1) a0
          in
          let hash:t_Array u32 (mk_usize 8) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize hash (mk_usize 2) b0
          in
          let hash:t_Array u32 (mk_usize 8) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize hash (mk_usize 3) c0
          in
          let hash:t_Array u32 (mk_usize 8) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize hash
              (mk_usize 4)
              (Core.Num.impl_u32__wrapping_add d0 t1 <: u32)
          in
          let hash:t_Array u32 (mk_usize 8) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize hash (mk_usize 5) e0
          in
          let hash:t_Array u32 (mk_usize 8) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize hash (mk_usize 6) f0
          in
          let hash:t_Array u32 (mk_usize 8) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize hash (mk_usize 7) g0
          in
          hash)
  in
  hash

let compress (block: t_Array u8 (mk_usize 64)) (hash: t_Array u32 (mk_usize 8))
    : t_Array u32 (mk_usize 8) =
  let s:t_Array u32 (mk_usize 64) = schedule block in
  let h_in:t_Array u32 (mk_usize 8) =
    Core.Clone.f_clone #(t_Array u32 (mk_usize 8)) #FStar.Tactics.Typeclasses.solve hash
  in
  let hash:t_Array u32 (mk_usize 8) = shuffle s hash in
  let hash:t_Array u32 (mk_usize 8) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 8)
      (fun hash temp_1_ ->
          let hash:t_Array u32 (mk_usize 8) = hash in
          let _:usize = temp_1_ in
          true)
      hash
      (fun hash i ->
          let hash:t_Array u32 (mk_usize 8) = hash in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize hash
            i
            (Core.Num.impl_u32__wrapping_add (hash.[ i ] <: u32) (h_in.[ i ] <: u32) <: u32)
          <:
          t_Array u32 (mk_usize 8))
  in
  hash

let u32s_to_be_bytes (state: t_Array u32 (mk_usize 8)) : t_Array u8 (mk_usize 32) =
  let (out: t_Array u8 (mk_usize 32)):t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32)
  in
  let out:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_LEN_SIZE
      (fun out temp_1_ ->
          let out:t_Array u8 (mk_usize 32) = out in
          let _:usize = temp_1_ in
          true)
      out
      (fun out i ->
          let out:t_Array u8 (mk_usize 32) = out in
          let i:usize = i in
          let tmp:u32 = state.[ i ] in
          let tmp:t_Array u8 (mk_usize 4) = Core.Num.impl_u32__to_be_bytes tmp in
          Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
            (mk_usize 4)
            (fun out temp_1_ ->
                let out:t_Array u8 (mk_usize 32) = out in
                let _:usize = temp_1_ in
                true)
            out
            (fun out j ->
                let out:t_Array u8 (mk_usize 32) = out in
                let j:usize = j in
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
                  ((i *! mk_usize 4 <: usize) +! j <: usize)
                  (tmp.[ j ] <: u8)
                <:
                t_Array u8 (mk_usize 32)))
  in
  out

let hash (msg: t_Slice u8)
    : Prims.Pure (t_Array u8 (mk_usize 32))
      (requires (cast (Core.Slice.impl__len #u8 msg <: usize) <: u64) <. mk_u64 2305843009213693951)
      (fun _ -> Prims.l_True) =
  let h:t_Array u32 (mk_usize 8) = v_HASH_INIT in
  let blocks:usize = (Core.Slice.impl__len #u8 msg <: usize) /! v_BLOCK_SIZE in
  let h:t_Array u32 (mk_usize 8) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      blocks
      (fun h temp_1_ ->
          let h:t_Array u32 (mk_usize 8) = h in
          let _:usize = temp_1_ in
          true)
      h
      (fun h i ->
          let h:t_Array u32 (mk_usize 8) = h in
          let i:usize = i in
          compress (Core.Result.impl__unwrap #(t_Array u8 (mk_usize 64))
                #Core.Array.t_TryFromSliceError
                (Core.Convert.f_try_into #(t_Slice u8)
                    #(t_Array u8 (mk_usize 64))
                    #FStar.Tactics.Typeclasses.solve
                    (msg.[ {
                          Core.Ops.Range.f_start = i *! v_BLOCK_SIZE <: usize;
                          Core.Ops.Range.f_end = (i +! mk_usize 1 <: usize) *! v_BLOCK_SIZE <: usize
                        }
                        <:
                        Core.Ops.Range.t_Range usize ]
                      <:
                      t_Slice u8)
                  <:
                  Core.Result.t_Result (t_Array u8 (mk_usize 64)) Core.Array.t_TryFromSliceError)
              <:
              t_Array u8 (mk_usize 64))
            h
          <:
          t_Array u32 (mk_usize 8))
  in
  let last_block_len:usize = (Core.Slice.impl__len #u8 msg <: usize) %! v_BLOCK_SIZE in
  let (last_block: t_Array u8 (mk_usize 64)):t_Array u8 (mk_usize 64) =
    Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 64)
  in
  let last_block:t_Array u8 (mk_usize 64) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range last_block
      ({ Core.Ops.Range.f_start = mk_usize 0; Core.Ops.Range.f_end = last_block_len }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (last_block.[ {
                Core.Ops.Range.f_start = mk_usize 0;
                Core.Ops.Range.f_end = last_block_len
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          (msg.[ { Core.Ops.Range.f_start = blocks *! v_BLOCK_SIZE <: usize }
              <:
              Core.Ops.Range.t_RangeFrom usize ]
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  let last_block:t_Array u8 (mk_usize 64) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize last_block
      last_block_len
      (mk_u8 128)
  in
  let _:Prims.unit = assert (Seq.length msg * 8 < pow2 64) in
  let len_bist:u64 = (cast (Core.Slice.impl__len #u8 msg <: usize) <: u64) *! mk_u64 8 in
  let len_bist_bytes:t_Array u8 (mk_usize 8) = Core.Num.impl_u64__to_be_bytes len_bist in
  let h, last_block:(t_Array u32 (mk_usize 8) & t_Array u8 (mk_usize 64)) =
    if last_block_len <. (v_BLOCK_SIZE -! v_LEN_SIZE <: usize)
    then
      let last_block:t_Array u8 (mk_usize 64) =
        Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
          v_LEN_SIZE
          (fun last_block temp_1_ ->
              let last_block:t_Array u8 (mk_usize 64) = last_block in
              let _:usize = temp_1_ in
              true)
          last_block
          (fun last_block i ->
              let last_block:t_Array u8 (mk_usize 64) = last_block in
              let i:usize = i in
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize last_block
                ((v_BLOCK_SIZE -! v_LEN_SIZE <: usize) +! i <: usize)
                (len_bist_bytes.[ i ] <: u8)
              <:
              t_Array u8 (mk_usize 64))
      in
      let h:t_Array u32 (mk_usize 8) = compress last_block h in
      h, last_block <: (t_Array u32 (mk_usize 8) & t_Array u8 (mk_usize 64))
    else
      let (pad_block: t_Array u8 (mk_usize 64)):t_Array u8 (mk_usize 64) =
        Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 64)
      in
      let pad_block:t_Array u8 (mk_usize 64) =
        Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
          v_LEN_SIZE
          (fun pad_block temp_1_ ->
              let pad_block:t_Array u8 (mk_usize 64) = pad_block in
              let _:usize = temp_1_ in
              true)
          pad_block
          (fun pad_block i ->
              let pad_block:t_Array u8 (mk_usize 64) = pad_block in
              let i:usize = i in
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize pad_block
                ((v_BLOCK_SIZE -! v_LEN_SIZE <: usize) +! i <: usize)
                (len_bist_bytes.[ i ] <: u8)
              <:
              t_Array u8 (mk_usize 64))
      in
      let h:t_Array u32 (mk_usize 8) = compress last_block h in
      let h:t_Array u32 (mk_usize 8) = compress pad_block h in
      h, last_block <: (t_Array u32 (mk_usize 8) & t_Array u8 (mk_usize 64))
  in
  u32s_to_be_bytes h

let sha256 (msg: t_Slice u8)
    : Prims.Pure (t_Array u8 (mk_usize 32))
      (requires (cast (Core.Slice.impl__len #u8 msg <: usize) <: u64) <. mk_u64 2305843009213693951)
      (fun _ -> Prims.l_True) = hash msg
