//! Tests on type aliases and type definitions
#![allow(dead_code)]
#![allow(unused_variables)]

// Basic type aliases
type UsizeAlias = usize;
type MyOption<A> = Option<A>;
type MyResult<A, B> = Result<Option<A>, B>;

// Monad-like type aliases
type ErrorMonad<A, E> = Result<A, E>;
type StateMonad<A, S> = (A, S);
type ESMonad<A, S, E> = StateMonad<ErrorMonad<A, E>, S>;

// Newtype wrappers
struct Meters(f64);
struct Seconds(f64);
struct Velocity(f64);

// Unit struct (zero-sized type)
struct Unit;
struct Marker;

fn make_unit() -> Unit {
    Unit
}

fn take_marker(_m: Marker) -> u32 {
    42
}

// Phantom data (generic but unused in data)
use core::marker::PhantomData;

struct Tagged<T> {
    value: u32,
    _phantom: PhantomData<T>,
}

struct Meters2;
struct Kilograms;

fn make_tagged_meters(v: u32) -> Tagged<Meters2> {
    Tagged {
        value: v,
        _phantom: PhantomData,
    }
}

fn make_tagged_kg(v: u32) -> Tagged<Kilograms> {
    Tagged {
        value: v,
        _phantom: PhantomData,
    }
}

fn read_tagged<T>(t: Tagged<T>) -> u32 {
    t.value
}

// Nested type aliases
type Pair<A> = (A, A);
type Triple<A> = (A, A, A);
type NestedPair<A> = Pair<Pair<A>>;
type OptionPair<A> = Option<Pair<A>>;

fn make_pair(x: u32) -> Pair<u32> {
    (x, x)
}

fn make_nested_pair(x: u32) -> NestedPair<u32> {
    ((x, x), (x, x))
}

fn unwrap_option_pair(x: OptionPair<u32>) -> u32 {
    match x {
        Some((a, b)) => a + b,
        None => 0,
    }
}

// Type alias in function signature
type Callback = fn(u32) -> u32;

fn apply(f: Callback, x: u32) -> u32 {
    f(x)
}

// Generic struct with multiple type params
struct Either<L, R> {
    is_left: bool,
    left: Option<L>,
    right: Option<R>,
}

fn make_left<L, R>(v: L) -> Either<L, R> {
    Either {
        is_left: true,
        left: Some(v),
        right: None,
    }
}

fn make_right<L, R>(v: R) -> Either<L, R> {
    Either {
        is_left: false,
        left: None,
        right: Some(v),
    }
}

// Recursive type via Box
enum Expr {
    Lit(i32),
    Add(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Neg(Box<Expr>),
}

fn eval(e: &Expr) -> i32 {
    match e {
        Expr::Lit(n) => *n,
        Expr::Add(a, b) => eval(a) + eval(b),
        Expr::Mul(a, b) => eval(a) * eval(b),
        Expr::Neg(a) => -eval(a),
    }
}

// Tuple struct with generic
struct Wrapper<T>(T);

fn wrap(x: u32) -> Wrapper<u32> {
    Wrapper(x)
}

fn unwrap(w: Wrapper<u32>) -> u32 {
    w.0
}

// Type alias for complex return types
type ParseResult<'a, T> = Result<(T, &'a str), &'a str>;

fn dummy_parse(input: &str) -> ParseResult<u32> {
    Ok((42, input))
}
