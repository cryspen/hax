This crate contains a partial model of Rust core that should preserve the same types signatures and behaviour as the original Rust core library. It only contains code that can be extracted with hax and used in `proof-libs` to give a model to Rust core items in the different hax backends.

## Contributing

Currently the only backend supported is F*, and the extracted models coexist with hand-written F* models. When a new module is added, the hand-written version should be deleted and replaced by the generated one. `.hax.sh extract` takes care of extracting and placing the result in `proof-libs`.

## Style considerations

Here is a list of things to pay attention to when contributing to the models:
* When using the `Fn` traits, the syntax shortcuts `Fn(T) -> U` are not available for the model traits. We need to write `Fn<T, Output = U>`
* The `core.mem.take` function cannot be given a good model that fits the Rust interface, we can only make it use unsafe or the original version, or change the interface to something corresponding to the interface of translated code (state passing instead of `&mut`).
