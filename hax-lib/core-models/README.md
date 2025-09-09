This crate contains a partial model of Rust core that should preserve the same types signatures and behaviour as the original Rust core library. It only contains code that can be extracted with hax and used in `proof-libs` to give a model to Rust core items in the different hax backends.

## Contributing

Currently the only backend supported is F*, and the extracted models coexist with hand-written F* models. When a new module is added, the hand-written version should be deleted and replaced by the generated one. `.hax.sh extract` takes care of extracting and placing the result in `proof-libs`.
