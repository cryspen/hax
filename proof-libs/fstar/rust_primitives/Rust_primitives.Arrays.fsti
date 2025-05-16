module Rust_primitives.Arrays

open Rust_primitives.Integers
open FStar.Mul

open FStar.FunctionalExtensionality    

type t_Slice (t: Type0) = (n:nat{n <= max_usize} & (i:nat {i < n} ^-> t))
type t_Array t (l:usize) = s: t_Slice t { let (| n, f |) = s in n == v l }

/// Create a slice
let createi (#t:Type0) (n:nat{n  <= max_usize}) (f: (i: nat {i < n}) -> t)
    : t_Slice t = (| n, on (i: nat {i < n}) f |)

/// Create a slice
let create (#t:Type0) (n:nat{n <= max_usize}) (v:t) : t_Slice t = 
  createi #t n (fun i -> v)

/// Empty slice
let empty #t : t_Slice t = createi 0 (fun i -> false_elim #t ())


/// Length of a slice
let length (#a: Type) (s: t_Slice a): n:nat{n <= max_usize} = let (| n, f |) = s in n


/// Indexing into a slice
let index #t (f: t_Slice t) (i:nat{i < length f}) : t = 
    let (| n, f |) = f in
    f i


/// Updating a slice
let upd #t (f: t_Slice t) (i:nat{i < length f}) (v:t) : t_Slice t = 
    createi (length f) (fun k -> if k = i then v else index f k)


/// Conversions to and from sequences
let of_seq #t (s: Seq.seq t{Seq.length s < max_usize}) : t_Slice t = 
    createi (Seq.length s) (fun i -> Seq.index s i)

let to_seq #t (f: t_Slice t) : Seq.seq t =
    let (| n, fa |) = f in
    FStar.Seq.init n (fun i -> fa i)

/// Converts an F* list into an array
let of_list (#t:Type) (l: list t {FStar.List.Tot.length l < max_usize}):
    t_Array t (sz (FStar.List.Tot.length l)) =
    createi (List.Tot.length l) (fun i -> List.Tot.index l i)

/// Converts an slice into a F* list
val to_list (#t:Type) (s: t_Slice t): list t

/// Equality

val eq #t (a b: t_Slice t) : r:bool{r <==> (a == b)}

/// Membership in a slice
val mem #t (x:t) (f: t_Slice t) : 
    b:bool {b <==> (exists i. index f i == x)}

/// Check whether a slice contains an item
let contains (#t: eqtype) (s: t_Slice t) (x: t): bool = 
  mem x s

/// Map a function 
let map #a #b (f:(x:a -> b)) (s: t_Slice a): t_Slice b
  = createi (length s) (fun i -> f (index s i))

let map_array #a #b #n (arr: t_Array a n) (f: a -> b): t_Array b n =
    map #a #b f arr

/// Introduce bitwise equality principle for sequences
let equal #t (a: t_Slice t) (b: t_Slice t) = a == b

val eq_intro #t (a : t_Slice t) (b:t_Slice t{length a == length b}):
       Lemma
       (requires forall i. {:pattern index a i; index b i}
                      i < length a ==>
                      index a i == index b i)
       (ensures equal a b)
       [SMTPat (equal a b)]
  

/// Cons and Snoc
let cons #t (v:t) (x:t_Slice t{length x < max_usize}):
            r:t_Slice t {length r == length x + 1} = 
    createi (length x + 1) (fun i -> if i = 0 then v else index x (i - 1))

let snoc #t (x:t_Slice t{length x < max_usize}) (v:t) :
            r:t_Slice t {length r == length x + 1} = 
    createi (length x + 1) (fun i -> if i < length x then index x i else v)


/// Concatenates two slices
let concat #t (x:t_Slice t) (y:t_Slice t{length x + length y <= max_usize}) :
           r:t_Slice t {length r == length x + length y} = 
    createi (length x + length y) (fun i -> if i < length x then index x i else index y (i - length x))


/// Take a subslice given `x` a slice and `i` and `j` two indexes
let slice #t (x:t_Slice t) (i:nat{i <= length x}) (j:nat{i <= j /\ j <= length x}):
           r:t_Slice t {length r == j - i} = 
    createi (j - i) (fun k -> index x (i + k))


/// Split a slice in two at index `m`
let split #t (a:t_Slice t) (m:nat{m <= length a}):
       Pure (t_Array t (sz m) & t_Array t (sz (length a - m)))
       True (ensures (fun (x,y) ->
         x == slice a 0 m /\
         y == slice a m (length a) /\
         concat #t x y == a) )= 
         let x = slice a 0 m in
         let y = slice a m (length a) in
         assert (equal a (concat x y));
         (x,y)

let lemma_slice_append #t (x:t_Slice t) (y:t_Slice t) (z:t_Slice t):
  Lemma (requires (length y + length z == length x /\
                   y == slice x 0 (length y) /\ 
                   z == slice x (length y) (length x)))
        (ensures (x == concat y z)) = 
        assert (equal x (concat y z))

let lemma_slice_append_3 #t (x:t_Slice t) (y:t_Slice t) (z:t_Slice t) (w:t_Slice t):
  Lemma (requires (length y + length z + length w == length x /\
                   y == slice x 0 (length y) /\ 
                   z == slice x (length y) (length y + length z) /\
                   w == slice x (length y + length z) (length x)))
        (ensures (x == concat y (concat z w))) =
         assert (equal x (concat y (concat z w)))

let lemma_slice_append_4 #t (x y z w u:t_Slice t) :
  Lemma (requires (length y + length z + length w + length u == length x /\
                   y == slice x 0 (length y) /\ 
                   z == slice x (length y) (length y + length z) /\
                   w == slice x (length y + length z) (length y + length z + length w) /\
                   u == slice x (length y + length z + length w) (length x)))
        (ensures (x == concat y (concat z (concat w u)))) =
         assert (equal x (concat y (concat z (concat w u))))


