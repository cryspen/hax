#![allow(dead_code)]
#![allow(unused_variables)]
// Tests on type aliases

type UsizeAlias = usize;
type MyOption<A> = Option<A>;
type MyResult<A, B> = Result<Option<A>, B>;

type ErrorMonad<A, E> = Result<A, E>;
type StateMonad<A, S> = (A, S);
type ESMonad<A, S, E> = StateMonad<ErrorMonad<A, E>, S>;
