This crate contains a partial model of Rust core that should preserve the same types signatures and behaviour as the original Rust core library. It only contains code that can be extracted with hax and used in `proof-libs` to give a model to Rust core items in the different hax backends.

## Contributing

Currently the only backend supported is F*, and the extracted models coexist with hand-written F* models. When a new module is added, the hand-written version should be deleted and replaced by the generated one. `.hax.sh extract` takes care of extracting and placing the result in `proof-libs`.

## Style considerations

Here is a list of things to pay attention to when contributing to the models:
* When using the `Fn` traits, the syntax shortcuts `Fn(T) -> U` are not available for the model traits. We need to write `Fn<T, Output = U>`
* The `core::mem::take`, `core::mem::swap`, etc. functions cannot be given a good model that fits the Rust interface, we can only use unsafe or the original version, or change the interface to something corresponding to the interface of translated code (state passing instead of `&mut`).

## Adding new models

To add new models, you should place yourself in the right module (create it if it doesn't already exist) corresponding to where it is located in Rust core. Then create the items with the same interface as in Rust (the Rust documentation is a good source of information, or sometimes the actual code). The interface can be slightly modified sometimes (removing `const`, or traits that we erase with hax). The code you write for the body can also be based on the real code if it is simple enough, or you can write something new that models the behaviour.

## Tests

This is a work in progress. All models should be executable, then the test strategy will be to test the model against its reference (probably with a property-based testing framework). Once the infrastructure is in place, all new models should come with tests. The extracted code should also be tested in each backend (to make sure the naming is correct, and basic proofs using the items can work).

## Relying on primitives

Some primitive operations are easier to model directly using the backend's language (integers, arithmetic, sequence-like data structures, etc.). This can happen in two different ways:
- Implicitly: integer types and arithmetic operations, array and slice types can be used directly. Hax has a special treatment of them, so any use in the core models implicitly refers to their implementation in Rust primitives (implemented manually for each backend)
- Explicitly: some more specific arithmetic operations, sequences, etc. are available in the rust_primitives crate. This crate provides all the other definitions that need a manual model in each backend. The definitions from this crate can be used in core models, but the crate itself is not extracted.

## Example

The `core::options` module is a good example. It mostly contains the definition of the `Option` enum which can be copied:

```Rust
pub enum Option<T> {
    Some(T),
    None,
}
```

Most functions can be defined in a very similar way to the original versions like:
```Rust
pub fn is_some(&self) -> bool {
    matches!(*self, Some(_))
}
```
The definition is exactly the same except that it is not `const`, and the attributes have been removed.

Whenever we take functions/closures as argument there is a bit more modification to be done. Indeed, we must use the `FnOnce` trait from our models and not the original one. For example:

```rust
pub const fn is_some_and(self, f: impl [const] FnOnce(T) -> bool + [const] Destruct) -> bool {
    match self {
        None => false,
        Some(x) => f(x),
    }
}
```
becomes
```rust
pub fn is_some_and<F: FnOnce<T, Output = bool>>(self, f: F) -> bool {
    match self {
        None => false,
        Some(x) => f.call_once(x),
    }
}
```
