module Alloc.Vec
open Rust_primitives

unfold type t_Vec t _ = s:slice t{Seq.length s <= max_usize}

let impl__new #t: t_Vec t () = FStar.Seq.empty

let impl_2__extend_from_slice #t (self: t_Vec t ()) (other: slice t{Seq.length self + Seq.length other <= max_usize}): t_Vec t ()
  = FStar.Seq.append self other

let impl__with_capacity (_capacity: usize) = impl__new

let impl_1__push
  (v: t_Vec 't ())// Removed: {Seq.length v + 1 <= max_usize})
  (x: 't)
  : t_Vec 't () = 
    FStar.Seq.append v (FStar.Seq.create 1 x)

let impl_1__len (v: t_Vec 't unit) =
  let n = Seq.length v in
  assert (n <= maxint usize_inttype);
  mk_int #usize_inttype (Seq.length v)

let from_elem (item: 'a) (len: usize) = Seq.create (v len) item

