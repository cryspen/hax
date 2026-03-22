module Rust_primitives.Arrays

open Rust_primitives.Integers
open FStar.Mul
open FStar.List.Tot.Properties

/// Helper: create a list of `n` copies of `x`
val list_create (#a: Type) (n: nat) (x: a): Tot (l:list a{FStar.List.Tot.length l == n})

/// Helper: create a list of `n` elements using a function
let rec list_init (#a: Type) (n: nat) (f: (i:nat{i < n}) -> a): Tot (l:list a{FStar.List.Tot.length l == n}) (decreases n)
  = if n = 0 then []
    else f 0 :: list_init (n-1) (fun (i:nat{i < n-1}) -> f (i+1))

/// Lemma: indexing into list_init
val list_init_index (#a: Type) (n: nat) (f: (i:nat{i < n}) -> a) (k: nat{k < n}):
  Lemma (ensures FStar.List.Tot.index (list_init n f) k == f k)
  [SMTPat (FStar.List.Tot.index (list_init n f) k)]

/// Helper: extract a sublist from index `i` to `j`
val list_slice (#a: Type) (l: list a) (i: nat) (j: nat{i <= j /\ j <= FStar.List.Tot.length l}):
  Tot (r:list a{FStar.List.Tot.length r == j - i})

/// Helper: update the element at index `i`
val list_upd (#a: Type) (l: list a) (i: nat{i < FStar.List.Tot.length l}) (x: a):
  Tot (r:list a{FStar.List.Tot.length r == FStar.List.Tot.length l})

/// Helper: append two lists, preserving length info in the return type
val list_append (#a: Type) (s1 s2: list a):
  Tot (r:list a{FStar.List.Tot.length r == FStar.List.Tot.length s1 + FStar.List.Tot.length s2})

/// Lemma: list_slice at empty range returns []
val list_slice_empty (#a: Type) (l: list a) (i: nat{i <= FStar.List.Tot.length l}):
  Lemma (list_slice l i i == [])
  [SMTPat (list_slice l i i)]

/// Lemma: indexing into list_create returns the value
val list_create_index (#a: Type) (n: nat) (x: a) (i: nat{i < n}):
  Lemma (FStar.List.Tot.index (list_create n x) i == x)
  [SMTPat (FStar.List.Tot.index (list_create n x) i)]

/// Lemma: indexing into list_upd at the updated position returns the new value,
/// and at other positions returns the original value
val list_upd_index (#a: Type) (l: list a) (i: nat{i < FStar.List.Tot.length l}) (x: a) (j: nat{j < FStar.List.Tot.length l}):
  Lemma (FStar.List.Tot.index (list_upd l i x) j == (if i = j then x else FStar.List.Tot.index l j))
  [SMTPat (FStar.List.Tot.index (list_upd l i x) j)]

/// Lemma: indexing into list_slice
val list_slice_index (#a: Type) (l: list a) (i: nat) (j: nat{i <= j /\ j <= FStar.List.Tot.length l}) (k: nat{k < j - i}):
  Lemma (FStar.List.Tot.index (list_slice l i j) k == FStar.List.Tot.index l (i + k))
  [SMTPat (FStar.List.Tot.index (list_slice l i j) k)]

/// Lemma: indexing into list_append
val list_append_index (#a: Type) (s1 s2: list a) (i: nat{i < FStar.List.Tot.length s1 + FStar.List.Tot.length s2}):
  Lemma (FStar.List.Tot.index (list_append s1 s2) i ==
    (if i < FStar.List.Tot.length s1
     then FStar.List.Tot.index s1 i
     else FStar.List.Tot.index s2 (i - FStar.List.Tot.length s1)))
  [SMTPat (FStar.List.Tot.index (list_append s1 s2) i)]

/// Rust slices and arrays are represented as lists
type t_Slice t = s:list t{FStar.List.Tot.length s <= max_usize}
type t_Array t (l:usize) = s: list t { FStar.List.Tot.length s == v l }

/// Length of a slice
let length (#a: Type) (s: t_Slice a): usize = sz (FStar.List.Tot.length s)

/// Check whether a slice contains an item
let contains (#t: eqtype) (s: t_Slice t) (x: t): bool = FStar.List.Tot.mem x s

/// Converts an F* list into an array
let of_list (#t:Type) (l: list t {FStar.List.Tot.length l < maxint U16}):
    t_Array t (sz (FStar.List.Tot.length l))
    = l

/// Converts a slice into an F* list
let to_list (#t:Type) (s: t_Slice t): list t = s

/// Maps a function over an array
val map_array (#a #b: Type) #n (arr: t_Array a n) (f: a -> b): t_Array b n

/// Creates an array of size `l` using a function `f`
let createi #t (l:usize) (f:(u:usize{u <. l} -> t))
    : t_Array t l
  = list_init (v l) (fun i -> f (sz i))

unfold let map #a #b #p
  (f:(x:a{p x} -> b))
  (s: t_Slice a {forall (i:nat). i < FStar.List.Tot.length s ==> p (FStar.List.Tot.index s i)}): t_Slice b
  = createi (length s) (fun i -> f (FStar.List.Tot.index s (v i)))

/// Concatenates two slices
#push-options "--fuel 1"
let concat #t (x:t_Slice t) (y:t_Slice t{range (v (length x) + v (length y)) usize_inttype}) :
           r:t_Array t (length x +! length y) =
  append_length x y;
  FStar.List.Tot.append x y
#pop-options

/// Translate indexes of `concat x y` into indexes of `x` or of `y`
val lemma_index_concat #t (x:t_Slice t) (y:t_Slice t{range (v (length x) + v (length y)) usize_inttype}) (i:usize{i <. length x +! length y}):
           Lemma (if i <. length x then
                    FStar.List.Tot.index (concat x y) (v i) == FStar.List.Tot.index x (v i)
                  else
                    FStar.List.Tot.index (concat x y) (v i) == FStar.List.Tot.index y (v (i -! length x)))
           [SMTPat (FStar.List.Tot.index (concat #t x y) (v i))]

/// Take a subslice given `x` a slice and `i` and `j` two indexes
let slice #t (x:t_Slice t) (i:usize{i <=. length x}) (j:usize{i <=. j /\ j <=. length x}):
           r:t_Array t (j -! i) = list_slice x (v i) (v j)

/// Translate indexes for subslices
val lemma_index_slice #t (x:t_Slice t) (i:usize{i <=. length x}) (j:usize{i <=. j /\ j <=. length x})
                                (k:usize{k <. j -! i}):
           Lemma (FStar.List.Tot.index (slice x i j) (v k) == FStar.List.Tot.index x (v (i +! k)))
           [SMTPat (FStar.List.Tot.index (slice x i j) (v k))]

/// Introduce pointwise equality principle for lists
val eq_intro #t (a : list t) (b:list t{FStar.List.Tot.length a == FStar.List.Tot.length b}):
       Lemma
       (requires forall i. {:pattern FStar.List.Tot.index a i; FStar.List.Tot.index b i}
                      i < FStar.List.Tot.length a ==>
                      FStar.List.Tot.index a i == FStar.List.Tot.index b i)
       (ensures a == b)
       [SMTPat (a == b)]

/// Split a slice in two at index `m`
val split #t (a:t_Slice t) (m:usize{m <=. length a}):
       Pure (t_Array t m & t_Array t (length a -! m))
       True (ensures (fun (x,y) ->
         x == slice a (sz 0) m /\
         y == slice a m (length a) /\
         concat #t x y == a))

val lemma_slice_append #t (x:t_Slice t) (y:t_Slice t) (z:t_Slice t):
  Lemma (requires (range (v (length y) + v (length z)) usize_inttype /\
                   length y +! length z == length x /\
                   y == slice x (sz 0) (length y) /\
                   z == slice x (length y) (length x)))
        (ensures (x == concat y z))

val lemma_slice_append_3 #t (x:t_Slice t) (y:t_Slice t) (z:t_Slice t) (w:t_Slice t):
  Lemma (requires (range (v (length y) + v (length z) + v (length w)) usize_inttype /\
                   length y +! length z +! length w == length x /\
                   y == slice x (sz 0) (length y) /\
                   z == slice x (length y) (length y +! length z) /\
                   w == slice x (length y +! length z) (length x)))
        (ensures (x == concat y (concat z w)))

val lemma_slice_append_4 #t (x y z w u:t_Slice t) :
  Lemma (requires (range (v (length y) + v (length z) + v (length w) + v (length u)) usize_inttype /\
                   length y +! length z +! length w +! length u == length x /\
                   y == slice x (sz 0) (length y) /\
                   z == slice x (length y) (length y +! length z) /\
                   w == slice x (length y +! length z) (length y +! length z +! length w) /\
                   u == slice x (length y +! length z +! length w) (length x)))
        (ensures (x == concat y (concat z (concat w u))))

