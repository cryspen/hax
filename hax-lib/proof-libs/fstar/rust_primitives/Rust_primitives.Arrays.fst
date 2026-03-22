module Rust_primitives.Arrays

open Rust_primitives.Integers
open FStar.Mul
open FStar.List.Tot.Properties

#set-options "--fuel 1 --ifuel 0 --z3rlimit 30"

let rec list_create (#a: Type) (n: nat) (x: a): Tot (l:list a{FStar.List.Tot.length l == n}) (decreases n)
  = if n = 0 then []
    else x :: list_create (n-1) x

(* list_init is defined in the .fsti for normalization *)

let list_init_index (#a: Type) (n: nat) (f: (i:nat{i < n}) -> a) (k: nat{k < n}):
  Lemma (ensures FStar.List.Tot.index (list_init n f) k == f k)
  [SMTPat (FStar.List.Tot.index (list_init n f) k)]
  = admit () // TODO: cannot prove here because .fsti makes list_init opaque to SMT in .fst

let rec list_slice (#a: Type) (l: list a) (i: nat) (j: nat{i <= j /\ j <= FStar.List.Tot.length l}):
  Tot (r:list a{FStar.List.Tot.length r == j - i}) (decreases (j - i))
  = if i = j then []
    else FStar.List.Tot.index l i :: list_slice l (i+1) j

let rec list_upd (#a: Type) (l: list a) (i: nat{i < FStar.List.Tot.length l}) (x: a):
  Tot (r:list a{FStar.List.Tot.length r == FStar.List.Tot.length l}) (decreases i)
  = match l with
    | hd :: tl -> if i = 0 then x :: tl else hd :: list_upd tl (i-1) x

let list_append (#a: Type) (s1 s2: list a):
  Tot (r:list a{FStar.List.Tot.length r == FStar.List.Tot.length s1 + FStar.List.Tot.length s2})
  = append_length s1 s2;
    FStar.List.Tot.append s1 s2

let list_slice_empty (#a: Type) (l: list a) (i: nat{i <= FStar.List.Tot.length l}):
  Lemma (list_slice l i i == [])
  [SMTPat (list_slice l i i)]
  = ()

let rec list_create_index (#a: Type) (n: nat) (x: a) (i: nat{i < n}):
  Lemma (ensures FStar.List.Tot.index (list_create n x) i == x)
        (decreases n)
  [SMTPat (FStar.List.Tot.index (list_create n x) i)]
  = if i = 0 then ()
    else list_create_index (n-1) x (i-1)

let rec list_upd_index (#a: Type) (l: list a) (i: nat{i < FStar.List.Tot.length l}) (x: a) (j: nat{j < FStar.List.Tot.length l}):
  Lemma (ensures FStar.List.Tot.index (list_upd l i x) j == (if i = j then x else FStar.List.Tot.index l j))
        (decreases i)
  [SMTPat (FStar.List.Tot.index (list_upd l i x) j)]
  = match l with
    | hd :: tl ->
      if i = 0 then ()
      else if j = 0 then ()
      else list_upd_index tl (i-1) x (j-1)

let rec lemma_index_list_slice (#a: Type) (l: list a) (i: nat) (j: nat{i <= j /\ j <= FStar.List.Tot.length l}) (k: nat{k < j - i}):
  Lemma (ensures FStar.List.Tot.index (list_slice l i j) k == FStar.List.Tot.index l (i + k))
        (decreases (j - i))
  = if k = 0 then ()
    else lemma_index_list_slice l (i+1) j (k-1)

let list_slice_index (#a: Type) (l: list a) (i: nat) (j: nat{i <= j /\ j <= FStar.List.Tot.length l}) (k: nat{k < j - i}):
  Lemma (FStar.List.Tot.index (list_slice l i j) k == FStar.List.Tot.index l (i + k))
  [SMTPat (FStar.List.Tot.index (list_slice l i j) k)]
  = lemma_index_list_slice l i j k

private let rec append_index_aux (#a: Type) (s1 s2: list a) (i: nat{i < FStar.List.Tot.length s1 + FStar.List.Tot.length s2}):
  Lemma (ensures (append_length s1 s2;
    FStar.List.Tot.index (FStar.List.Tot.append s1 s2) i ==
    (if i < FStar.List.Tot.length s1
     then FStar.List.Tot.index s1 i
     else FStar.List.Tot.index s2 (i - FStar.List.Tot.length s1))))
  (decreases (FStar.List.Tot.length s1))
  = match s1 with
    | [] -> ()
    | _ :: tl ->
      append_length s1 s2;
      if i = 0 then ()
      else (append_length tl s2; append_index_aux tl s2 (i - 1))

let list_append_index (#a: Type) (s1 s2: list a) (i: nat{i < FStar.List.Tot.length s1 + FStar.List.Tot.length s2}):
  Lemma (FStar.List.Tot.index (list_append s1 s2) i ==
    (if i < FStar.List.Tot.length s1
     then FStar.List.Tot.index s1 i
     else FStar.List.Tot.index s2 (i - FStar.List.Tot.length s1)))
  [SMTPat (FStar.List.Tot.index (list_append s1 s2) i)]
  = append_index_aux s1 s2 i

let map_array (#a #b: Type) #n (arr: t_Array a n) (f: a -> b): t_Array b n
  = list_init (v n) (fun i -> f (FStar.List.Tot.index arr i))

(* list_init_index and createi are now defined in the .fsti for normalization *)

#push-options "--fuel 2 --z3rlimit 60"

let lemma_index_concat #t (x:t_Slice t) (y:t_Slice t{range (v (length x) + v (length y)) usize_inttype}) (i:usize{i <. length x +! length y}):
           Lemma (if i <. length x then
                    FStar.List.Tot.index (concat x y) (v i) == FStar.List.Tot.index x (v i)
                  else
                    FStar.List.Tot.index (concat x y) (v i) == FStar.List.Tot.index y (v (i -! length x)))
           [SMTPat (FStar.List.Tot.index (concat #t x y) (v i))]
  = admit () // TODO: prove via induction on x

let lemma_index_slice #t (x:t_Slice t) (i:usize{i <=. length x}) (j:usize{i <=. j /\ j <=. length x})
                                (k:usize{k <. j -! i}):
           Lemma (FStar.List.Tot.index (slice x i j) (v k) == FStar.List.Tot.index x (v (i +! k)))
           [SMTPat (FStar.List.Tot.index (slice x i j) (v k))]
  = lemma_index_list_slice x (v i) (v j) (v k)

#pop-options

let eq_intro #t (a : list t) (b:list t{FStar.List.Tot.length a == FStar.List.Tot.length b}):
       Lemma
       (requires forall i. {:pattern FStar.List.Tot.index a i; FStar.List.Tot.index b i}
                      i < FStar.List.Tot.length a ==>
                      FStar.List.Tot.index a i == FStar.List.Tot.index b i)
       (ensures a == b)
       [SMTPat (a == b)]
  = admit () // TODO: prove by induction on lists

let split #t (a:t_Slice t) (m:usize{m <=. length a}):
       Pure (t_Array t m & t_Array t (length a -! m))
       True (ensures (fun (x,y) ->
         x == slice a (sz 0) m /\
         y == slice a m (length a) /\
         concat #t x y == a))
  = admit (); // TODO
    let x = list_slice a 0 (v m) in
    let y = list_slice a (v m) (FStar.List.Tot.length a) in
    (x, y)

let lemma_slice_append #t (x:t_Slice t) (y:t_Slice t) (z:t_Slice t):
  Lemma (requires (range (v (length y) + v (length z)) usize_inttype /\
                   length y +! length z == length x /\
                   y == slice x (sz 0) (length y) /\
                   z == slice x (length y) (length x)))
        (ensures (x == concat y z))
  = admit () // TODO

let lemma_slice_append_3 #t (x:t_Slice t) (y:t_Slice t) (z:t_Slice t) (w:t_Slice t):
  Lemma (requires (range (v (length y) + v (length z) + v (length w)) usize_inttype /\
                   length y +! length z +! length w == length x /\
                   y == slice x (sz 0) (length y) /\
                   z == slice x (length y) (length y +! length z) /\
                   w == slice x (length y +! length z) (length x)))
        (ensures (x == concat y (concat z w)))
  = admit () // TODO

let lemma_slice_append_4 #t (x y z w u:t_Slice t) :
  Lemma (requires (range (v (length y) + v (length z) + v (length w) + v (length u)) usize_inttype /\
                   length y +! length z +! length w +! length u == length x /\
                   y == slice x (sz 0) (length y) /\
                   z == slice x (length y) (length y +! length z) /\
                   w == slice x (length y +! length z) (length y +! length z +! length w) /\
                   u == slice x (length y +! length z +! length w) (length x)))
        (ensures (x == concat y (concat z (concat w u))))
  = admit () // TODO
