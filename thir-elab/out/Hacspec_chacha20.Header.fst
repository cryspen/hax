module Hacspec_chacha20.Header

open FStar.Mul
open Hacspec.Lib

unfold type state_t = lseq uint32 16
unfold type state_idx = nat_mod 16

unfold type constants_t = lseq uint32 4
unfold type constants_idx = nat_mod 4

unfold type block_t = lseq uint8 64
unfold type chaChaIV_t = lseq uint8 12
unfold type chaChaKey_t = lseq uint8 32

class from_seq_tc (t: Type) 
  = { inner: Type
    ; size: nat
    ; from_seq: s:seq inner{seq_len s = size} -> t }
class array_assign (o: Type0) 
  = { key: Type0
    ; value: Type0
    ; (.[]<-): o -> key -> value -> o }
class has_new_ (o: Type) = {new_: o}

instance from_seq_lseq inner size: from_seq_tc (lseq inner size) 
  = { inner; size
    ; from_seq = array_from_seq size }
    
instance array_lseq value (s: uint_size {s > 0}): array_assign (lseq value s)
  = { value; key = nat_mod s
    ; (.[]<-) = array_upd }

instance has_new_uint64: has_new_ uint64 = {new_ = secret (pub_u64 0)}
instance has_new_uint32: has_new_ uint32 = {new_ = secret (pub_u32 0)}b
instance has_new_uint16: has_new_ uint16 = {new_ = secret (pub_u16 0)}
instance has_new_uint8: has_new_ uint8 = {new_ = secret (pub_u8 0)}
instance has_new_int64: has_new_ int64 = {new_ = secret (pub_i64 0)}
instance has_new_int32: has_new_ int32 = {new_ = secret (pub_i32 0)}
instance has_new_int16: has_new_ int16 = {new_ = secret (pub_i16 0)}
instance has_new_int8: has_new_ int8 = {new_ = secret (pub_i8 0)}

instance has_new_lseq {| has_new_ 'a |} s: has_new_ (lseq 'a s) 
  = {new_ = array_new_ new_ s}

let to_le_bytes (#int_ty: inttype{unsigned int_ty /\ int_ty <> U1})
  (#len: uint_size{
    range (len * (match int_ty with U8 -> 1 | U16 -> 2  | U32 -> 4 | U64 -> 8 | U128 -> 16)) U32
  })
  = array_to_le_bytes #int_ty #len

let to_le_U32s = array_to_le_uint32s


class xor (t: Type) = { (^.): t -> t -> t }
instance xor_inherit t l: xor (int_t t l) = { (^.) = logxor }
instance xor_lseq (len: uint_size) (t:Type) {| xor t |}: xor (lseq t len) 
  = { (^.) = array_xor (^.) }

class add (t: Type) = { (+.): t -> t -> t }

instance _: add int = { (+.) = (+) }
instance add_inherit (t:inttype{unsigned t}) l: add (int_t t l) = { (+.) = add_mod }
instance add_lseq (len: uint_size) (t:Type) {| add t |}: add (lseq t len) 
  = { (+.) = array_add (+.) }

let slice = array_slice

// class foldi_tc (key: eqtype) = {
//   foldi_lt_key: key -> key -> bool;
//   pred: key -> Type;
//   foldi: (#a: Type) -> 
//          (lo: key {pred lo}) ->
//          (hi: key{pred hi /\ lo `foldi_lt_key` hi \/ lo == hi}) ->
//          (f: (i:key{pred i /\ i `foldi_lt_key` hi}) -> a -> a) ->
//          (init: a) -> a
// }

// unfold instance foldi_int: foldi_tc int = {
//   foldi_lt_key = (<=);
//   pred = (fun x -> range x U32);
//   foldi = Hacspec.Lib.foldi
// }
// unfold instance foldi_range_t_u32: foldi_tc (range_t U32) = {
//   foldi_lt_key = (<=);
//   pred = (fun x -> True);
//   foldi = Hacspec.Lib.foldi
// }
// unfold instance _: foldi_tc Int32.t =
//   let foldi_lt_key = (fun x y -> Int32.lt x y) in
//   let pred = (fun x -> range (Int32.v x) U32) in
//   let foldi (#a: Type)
//          (lo: Int32.t {pred lo})
//          (hi: Int32.t{pred hi /\ lo `foldi_lt_key` hi \/ lo == hi})
//          (f: (i:Int32.t{pred i /\ i `foldi_lt_key` hi}) -> a -> a)
//          (init: a) = 
//            Hacspec.Lib.foldi #a (Int32.v lo) (Int32.v hi) 
//                                      (fun i -> f (Int32.int_to_t i)) init
//          in
//   {
//   foldi_lt_key;
//   pred;
//   foldi
// }
