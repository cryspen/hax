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
