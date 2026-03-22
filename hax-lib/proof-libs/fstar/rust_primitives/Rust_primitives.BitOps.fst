module Rust_primitives.BitOps

open FStar.Mul

#set-options "--fuel 1 --ifuel 0 --z3rlimit 30"

let rec nat_logand (a b: nat) (n: nat): Tot (r:nat{r < pow2 n}) (decreases n) =
  if n = 0 then 0
  else
    let r = nat_logand (a / 2) (b / 2) (n - 1) in
    2 * r + (a % 2) * (b % 2)

let rec nat_logor (a b: nat) (n: nat): Tot (r:nat{r < pow2 n}) (decreases n) =
  if n = 0 then 0
  else
    let r = nat_logor (a / 2) (b / 2) (n - 1) in
    let bit = (if a % 2 + b % 2 > 0 then 1 else 0) in
    2 * r + bit

let rec nat_logxor (a b: nat) (n: nat): Tot (r:nat{r < pow2 n}) (decreases n) =
  if n = 0 then 0
  else
    let r = nat_logxor (a / 2) (b / 2) (n - 1) in
    2 * r + ((a + b) % 2)

let rec nat_lognot (a: nat) (n: nat): Tot (r:nat{r < pow2 n}) (decreases n) =
  if n = 0 then 0
  else
    let r = nat_lognot (a / 2) (n - 1) in
    2 * r + (1 - a % 2)

let rec count_ones_nat (x: nat) (n: nat): Tot (r:nat{r <= n}) (decreases n) =
  if n = 0 then 0
  else (x % 2) + count_ones_nat (x / 2) (n - 1)

let rec pow_nat (base: int) (exp: nat): Tot int (decreases exp) =
  if exp = 0 then 1
  else base * pow_nat base (exp - 1)
