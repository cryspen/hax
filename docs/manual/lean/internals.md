---
weight: 102
---

# Internals

The encoding of Rust in Lean has three main components:

* the *syntax* (items, functions, `if`-`else`, `match`, etc), defined by the *backend*
  ([`/rust-engine/src/backends/lean.rs`](https://github.com/cryspen/hax/blob/main/rust-engine/src/backends/lean.rs))
* the *primitives/intrinsics* (`u32`, `isize`, slices, etc) defined by in the *Prelude*
  ([`hax-lib/proof-libs/lean`](https://github.com/cryspen/hax/tree/main/hax-lib/proof-libs/lean))
* the models of *core* and *std* libraries.

While mostly separated, the Backend make some assumption on the Prelude,
typically when it inserts notations for some symbol (i.e. `+?` for addition).

[!Disclaimer] : The lean backend is still experimental. See the list of [open
issues](https://github.com/cryspen/hax/issues?q=is%3Aissue%20state%3Aopen%20label%3Alean)
for known problems and workaround. See also the [Hax
Zulip](https://hacspec.zulipchat.com/) for technical support.

## Backend

### Monadic encoding

All rust computations can panic or diverge, while Lean ones cannot (by
default). To account for this, Rust types are wrapped inside a
[monad](https://en.wikipedia.org/wiki/Monad_(functional_programming)) that
represents the possible results:

```lean
inductive Error where
   | assertionFailure: Error
   | integerOverflow: Error
   | divisionByZero: Error
   | arrayOutOfBounds: Error
   | maximumSizeExceeded: Error
   | panic: Error
   | undef: Error

inductive Result.{u} (α : Type u) where
  | ok (v: α): Result α
  | fail (e: Error): Result α
  | div
```

This monadic encoding shows for simple expressions: the result of the lean
extracted function is not `u32` but `Result u32`.

/// html | div[style='float: left; width: 48%;']
```rust
fn f (x: u32) -> u32 {
    x + 1
}
```
///

/// html | div[style='float: right;width: 48%;']
```lean
def f (x : u32) : Result u32
  := do (← x +? (1 : u32))
```
///

/// html | div[style='clear: both;']
///

The backend relies on the
[do-notation](https://lean-lang.org/doc/reference/latest//Functors___-Monads-and--do--Notation/Syntax/#do-notation):
all functions start with the `do` keyword, indicating that the sequence of bindings should
actually be understood as bindings in the monad, propagating potential
errors to the top.

The `do` keywords enables the lifting `←` and the `pure` operators. Intuitively,
lifting turns a value of type `Result T` into a value of type `T` by turning the
rest of the program into a use of `bind`. Conversely, `pure` turns a value of
type `T` into a value of type `Result T`. This shows also for let-bindings :


/// html | div[style='float: left; width: 48%;']
```rust
fn f (x: u32) -> u32 {
    let y = x + 1;
    let z = y + 1;
    y + z
}
```
///

/// html | div[style='float: right;width: 48%;']
```lean
def f (x : u32) : Result u32 := do
  let y : u32 ← (pure
    (← x +? (1 : u32)));
  let z : u32 ← (pure
    (← y +? (1 : u32)));
  (← y +? z)
```
///

/// html | div[style='clear: both;']
///


Currently, the backend does not try to be parsimonious with the introduction of `pure` and `←`.

### Structs

#### Type definitions

Rust structs are encoded as [Lean
structures](https://lean-lang.org/doc/reference/latest//The-Type-System/Inductive-Types/#structures). The
special case of [tuple
structs](https://doc.rust-lang.org/book/ch05-01-defining-structs.html#using-tuple-structs-without-named-fields-to-create-different-types)
are also encoded as Lean structures, where the fields are numbered : `_0`, `_1`,
etc. See for instance :

/// html | div[style='float: left; width: 48%;']

```rust
struct S1 {
    f1: usize,
    f2: usize,
}

struct S2 {
    f1: S1,
    f2: usize,
}

// Tuple structs
struct T0();
struct T1<A>(A);
struct T2<A, B>(A, B);
struct T3<A, B, C>(A, B, C);
struct T3p<A, B, C>(A, T2<B, C>);
```
///

/// html | div[style='float: right;width: 48%;']
```lean
structure S1 where
  f1 : usize
  f2 : usize

structure S2 where
  f1 : S1
  f2 : usize

structure T0 where
structure T1 A where
  _0 : A
structure T2 A B where
  _0 : A
  _1 : B
structure T3 A B C where
  _0 : A
  _1 : B
  _2 : C
structure T3p A B C where
  _0 : A
  _1 : (T2 B C)
```
///

/// html | div[style='clear: both;']
///

#### Expressions, accessors and pattern-matching

Building, accessing and destructing structs :

/// html | div[style='float: left; width: 48%;']
```rust
// Building
let s1 = S1 { f1: 0, f2: 1 };

let t3 = T3(T0(), T1(1), T2(1, 2));

// Matching
let S1 { f1, f2 } = s1;

let T3(T0(), T1(_), T2(_, _)) = t3;

// Accessing
let _ = (s1.f1, s1.f2);

let _ = t3.0;
let _ = t3.1;
let _ = t3.2;
let _ = t3.2.1;

```
///

/// html | div[style='float: right;width: 48%;']

```lean
-- Building
let s1 : S1 ← (pure
  (S1.mk
    (f1 := (0 : usize))
    (f2 := (1 : usize))));

let t3 :
  (T3 T0 (T1 i32) (T2 i32 i32))
  ← (pure
      (T3.mk
        T0.mk
        (T1.mk (1 : i32))
        (T2.mk
          (1 : i32)
          (2 : i32))));

-- Matching
let ({f1 := (f1 : usize),
      f2 := (f2 : usize)} : S1) ←
  (pure s1);

let (⟨(⟨⟩ : T0),
      (⟨(_ : i32)⟩ : (T1 i32)),
      (⟨(_ : i32), (_ : i32)⟩
        : (T2 i32 i32))⟩ :
    (T3 T0 (T1 i32) (T2 i32 i32))) ←
  (pure t3);

-- Accessing
let (_ : (Tuple2 usize usize)) ←
  (pure
    (Tuple2.mk
      (S1.f1 s1)
      (S1.f2 s1)));

let (_ : i32) ← (pure
  (T2._1 t2));
let (_ : T0) ← (pure
  (T3._0 t3));
let (_ : (T1 i32)) ← (pure
  (T3._1 t3));
let (_ : (T2 i32 i32)) ← (pure
  (T3._2 t3));
let (_ : i32) ← (pure
  (T2._1 (T3._2 t3)));
```
///

/// html | div[style='clear: both;']
///

### Enums

#### Type definitions

Rust enums are encoded as [Lean inductive
types](https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#inductive-types). Variants
with record fields use *named* arguments, whereas variants with tuple fields use
normal positional arguments.


/// html | div[style='float: left; width: 48%;']
```rust
// 1. Type definition
enum E {
    // unit-like
    V1,
    V2,
    // with positional arguments
    V3(usize),
    V4(usize, usize, usize),
    // with named arguments
    V5 { f1: usize, f2: usize },
    V6 { f1: usize, f2: usize },
}
```
///

/// html | div[style='float: right;width: 48%;']

```lean
inductive E : Type
| V1  : E
| V2  : E
| V3  : usize -> E
| V4  : usize -> usize -> usize -> E
| V5 (f1 : usize) (f2 : usize) : E
| V6 (f1 : usize) (f2 : usize) : E
```
///

/// html | div[style='clear: both;']
///

#### Expressions and pattern-matching

/// html | div[style='float: left;width: 48%;']

```rust
// Building
let e_v1 = E::V1;
let e_v2 = E::V2;
let e_v3 = E::V3(23);
let e_v4 = E::V4(23, 12, 1);
let e_v5 = E::V5 { f1: 23, f2: 43 };
let e_v6 = E::V6 { f1: 12, f2: 13 };

// Matching
match e_v1 {
    E::V1 => (),
    E::V2 => (),
    E::V3(_) => (),
    E::V4(x1, x2, x3) => {
        let y1 = x1 + x2;
        let y2 = y1 - x2;
        let y3 = y2 + x3;
        ()
    }
    E::V5 { f1, f2 } => (),
    E::V6 {
        f1,
        f2: other_name_for_f2,
    } => (),
}
```
///

/// html | div[style='float: right;width: 48%;']
```lean
def enums (_ : Tuple0)
  : Result Tuple0
  := do
  let e_v1 : E ← (pure E.V1);
  let e_v2 : E ← (pure E.V2);
  let e_v3 : E ← (pure
    (E.V3 (23 : usize)));
  let e_v4 : E ← (pure
    (E.V4
      (23 : usize)
      (12 : usize)
      (1 : usize)));
  let e_v5 : E ← (pure
    (E.V5
      (f1 := (23 : usize))
      (f2 := (43 : usize))));
  let e_v6 : E ← (pure
    (E.V6
      (f1 := (12 : usize))
      (f2 := (13 : usize))));
  (match e_v1 with
    | (E.V1 ) => do Tuple0.mk
    | (E.V2 ) => do Tuple0.mk
    | (E.V3 (_ : usize))
      => do Tuple0.mk
    | (E.V4
        (x1 : usize)
        (x2 : usize)
        (x3 : usize))
      => do
        let y1 : usize ← (pure
          (← x1 +? x2));
        let y2 : usize ← (pure
          (← y1 -? x2));
        let y3 : usize ← (pure
          (← y2 +? x3));
        Tuple0.mk
    | (E.V5
        (f1 := (f1 : usize))
        (f2 := (f2 : usize)))
      => do Tuple0.mk
    | (E.V6
        (f1 := (f1 : usize))
        (f2 :=
          (other_name_for_f2 : usize)))
      => do Tuple0.mk)
```
///

/// html | div[style='clear: both;']
///
### Traits

Rust traits are represented as Lean classes, while Rust impl are Lean
instances. The Lean code relies on the typeclass inference of Lean. Hax exposes
identifiers for rust impls (that are otherwise implicit), like
`8040238289193487104`. Lean uses them for naming fields or parameters.


/// html | div[style='float: left; width: 48%;']

```rust
trait T1 {
    fn f1(&self) -> usize;
    fn f2(&self, y: &Self) -> usize;
}

struct S;

impl T1 for S {
    fn f1(&self) -> usize {
        42
    }
 fn f2(&self, y: &Self) -> usize {
        43
    }
}

fn f<T: T1>(x: T) -> usize {
    x.f1() + x.f2(&x)
}
```
///

/// html | div[style='float: right;width: 48%;']
```lean
class T1 (Self : Type) where
  f1 : Self -> Result usize
  f2 : Self -> Self -> Result usize

structure S where

instance Impl : T1 S where
  f1 (self : S)
    := do (42 : usize)
  f2 (self : S) (y : S)
    := do (43 : usize)

def f (T : Type) [(T1 T)] (x : T)
  : Result usize
  := do
  (← (← T1.f1 x) +? (← T1.f2 x x))
```
///

/// html | div[style='clear: both;']
///


#### Supertraits

Super trait bounds are represented as extra fields


/// html | div[style='float: left; width: 48%;']
```rust
trait Test<T: T1>: T2 {
   fn f_test(&self, x: &T) -> usize;
}
```
///

/// html | div[style='float: right;width: 48%;']
```lean
class Test
  (Self : Type)
  (T : Type)
  where
  [_constr_8040238289193487104 :
    (T2 Self)]
  [_constr_7570495343596639253 :
    (T1 T)]
  f_test :
    Self -> T -> Result usize
```
///

/// html | div[style='clear: both;']
///

#### Associated types

The support for associated types is currently restricted to types defined within
the current trait


/// html | div[style='float: left; width: 48%;']
```rust
mod associated_types {
    trait T1 {
        type T;
        fn f(&self, x: Self::T) -> Self::T;
    }

    trait T2 {
        type T: T1;
        fn f(&self, x: Self::T) -> usize;
    }

    trait Foo<T> {}
    trait Bar {}

    trait T3 {
        type T: Foo<()>;
        type Tp<T: Bar>: Foo<T>;
        fn f<A: Bar>(&self, x: Self::T, y: Self::Tp<A>) -> usize;
    }
}
```
///

/// html | div[style='float: right;width: 48%;']
```lean
class Foo (Self : Type) (T : Type) where


class Bar (Self : Type) where


class T1 (Self : Type) where
  T : Type
  f : Self -> T -> Result T

class T3 (Self : Type) where
  T : Type
  [_constr_13086648656846024831 :
    (Foo T Tuple0)]
  Tp : Type
  [_constr_15450263461214744089 : (Foo Tp T)]
  f (A : Type) [(Bar A)] :
    Self -> T -> Tp -> Result usize

class T2 (Self : Type) where
  T : Type
  [_constr_18277713886489441014 : (T1 T)]
  f : Self -> T -> Result usize

```
///

/// html | div[style='clear: both;']
///


## Prelude

See the [Hax Lean library](https://github.com/cryspen/hax/tree/main/hax-lib/proof-libs/lean)
