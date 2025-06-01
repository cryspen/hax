module Sha256

#set-options "--max_fuel 25 --max_ifuel 25 --z3rlimit 60 --query_stats"

open Core

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

let v_OP_TABLE: t_OpTableType =
  let list =
    [
      mk_u8 2; mk_u8 13; mk_u8 22; mk_u8 6; mk_u8 11; mk_u8 25; mk_u8 7; mk_u8 18; mk_u8 3; mk_u8 17;
      mk_u8 19; mk_u8 10
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 12);
  Rust_primitives.Hax.array_of_list 12 list

let v_K_TABLE: t_RoundConstantsTable =
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

let v_HASH_INIT: t_Hash =
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

let ch (x y z: u32) : u32 = (x &. y) ^. (~.x &. z)

let maj (x y z: u32) : u32 = (x &. y) ^. (x &. z) ^. (y &. z)

let sigma (x: u32) (i: usize{i <. mk_usize 4}) (op: usize) : u32 =
  let tmp:u32 =
    x >>>.
    Core.Convert.f_into #u8
      #u32
      #FStar.Tactics.Typeclasses.solve
      (v_OP_TABLE.[ (mk_usize 3) *! i +! (mk_usize 2) ] <: u8)
  in
  let tmp:u32 =
    if op =. mk_usize 0 then x >>! (v_OP_TABLE.[ (mk_usize 3) *! i +! (mk_usize 2) ] <: u8) else tmp
  in
  let rot_val_1:u32 =
    Core.Convert.f_into #u8 #u32 #FStar.Tactics.Typeclasses.solve v_OP_TABLE.[ (mk_usize 3) *! i ]
  in
  let rot_val_2:u32 =
    Core.Convert.f_into #u8
      #u32
      #FStar.Tactics.Typeclasses.solve
      v_OP_TABLE.[ (mk_usize 3) *! i +! (mk_usize 1) ]
  in
  // TODO: Figure out why <: u32 is needed here twice
  (x >>>. rot_val_1 <: u32) ^. (x >>>. rot_val_2 <: u32) ^. tmp

let to_be_u32s (block: t_Block) : Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global =
  let out:Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global =
    Alloc.Vec.impl__with_capacity #u32 (v_BLOCK_SIZE /! mk_usize 4)
  in
  let out:Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Slice.impl__chunks_exact
              #u8
              block
              (mk_usize 4)))
      out
      (fun out block_chunk ->
          let out:Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global = out in
          let block_chunk_array =
            Core.Num.impl_u32__from_be_bytes (Core.Result.impl__unwrap #(t_Array u8 (mk_usize 4))
                  (Core.Convert.f_try_into #(t_Slice u8) #(t_Array u8 (mk_usize 4)) block_chunk))
          in
          let out:Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global =
            Alloc.Vec.impl_1__push #u32 #Alloc.Alloc.t_Global out block_chunk_array
          in
          out)
  in
  out

let schedule (block: t_Block) : t_RoundConstantsTable =
  let b = to_be_u32s block in
  let s: t_RoundConstantsTable = Rust_primitives.Hax.repeat (mk_u32 0) (mk_usize 64) in
  let s: t_RoundConstantsTable =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 16)
      (fun _ _ -> true)
      s
      (fun s (i: usize) ->
          let s: t_RoundConstantsTable = s in
          if i <. mk_usize 16 <: b bool
          then
            let s: t_RoundConstantsTable =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s i b.[ i ]
            in
            s
          else
            let t16:u32 = s.[ i -! mk_usize 16 ] in
            let t15:u32 = s.[ i -! mk_usize 15 ] in
            let t7:u32 = s.[ i -! mk_usize 7 ] in
            let t2:u32 = s.[ i -! mk_usize 2 ] in
            let s1:u32 = sigma t2 (mk_usize 3) (mk_usize 0) in
            let s0:u32 = sigma t15 (mk_usize 2) (mk_usize 0) in
            let s: t_RoundConstantsTable =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
                i
                (s1 +. t7 +. s0 +. t16)
            in
            s)
  in
  s

let shuffle (ws: t_RoundConstantsTable) (hashi: t_Hash) : t_Hash =
  let h: t_Hash = hashi in
  let h: t_Hash =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_K_SIZE
      (fun _ _ -> true)
      h
      (fun (h: t_Array u32 (mk_usize 8)) i ->
          let a0:u32 = h.[ mk_usize 0 ] in
          let b0:u32 = h.[ mk_usize 1 ] in
          let c0:u32 = h.[ mk_usize 2 ] in
          let d0:u32 = h.[ mk_usize 3 ] in
          let e0:u32 = h.[ mk_usize 4 ] in
          let f0:u32 = h.[ mk_usize 5 ] in
          let g0:u32 = h.[ mk_usize 6 ] in
          let h0:u32 = h.[ mk_usize 7 ] in
          let t1:u32 =
            h0 +. (sigma e0 (mk_usize 1) (mk_usize 1)) +. (ch e0 f0 g0) +. v_K_TABLE.[ i ]
          in
          let t2:u32 = (sigma a0 (mk_usize 0) (mk_usize 1)) +. (maj a0 b0 c0) in
          let h:t_Array u32 (mk_usize 8) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize h (mk_usize 0) (t1 +. t2)
          in
          let h:t_Array u32 (mk_usize 8) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize h (mk_usize 1) a0
          in
          let h:t_Array u32 (mk_usize 8) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize h (mk_usize 2) b0
          in
          let h:t_Array u32 (mk_usize 8) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize h (mk_usize 3) c0
          in
          let h:t_Array u32 (mk_usize 8) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize h (mk_usize 4) (d0 +. t1)
          in
          let h:t_Array u32 (mk_usize 8) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize h (mk_usize 5) e0
          in
          let h:t_Array u32 (mk_usize 8) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize h (mk_usize 6) f0
          in
          let h:t_Array u32 (mk_usize 8) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize h (mk_usize 7) g0
          in
          h)
  in
  h

let compress (block: t_Block) (h_in: t_Hash) : t_Hash =
  let s: t_RoundConstantsTable = schedule block in
  let h: t_Hash = shuffle s h_in in
  let h: t_Hash =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 8)
      (fun _ _ -> true)
      h
      (fun (h: t_Array u32 (mk_usize 8)) i ->
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize h i (h.[ i ] +. h_in.[ i ]))
  in
  h

let u32s_to_be_bytes (state: t_Hash) : t_Sha256Digest =
  let out: t_Sha256Digest = Rust_primitives.Hax.repeat (mk_u8 0) v_HASH_SIZE in
  let out: t_Sha256Digest =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_LEN_SIZE
      (fun _ _ -> true)
      out
      (fun (out: t_Sha256Digest) i ->
          let tmp:u32 = state.[ i ] in
          let tmp:t_Array u8 (mk_usize 4) = Core.Num.impl_u32__to_be_bytes tmp in
          Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
            (mk_usize 4)
            (fun _ _ -> true)
            out
            (fun (out: t_Sha256Digest) j ->
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
                  ((i *! mk_usize 4) +! j)
                  (tmp.[ j ])))
  in
  out
  
// TOOD
let hash (msg: t_Slice u8) : t_Sha256Digest = admit()

let sha256 (msg: t_Slice u8) : t_Array u8 (mk_usize 32) = hash msg
