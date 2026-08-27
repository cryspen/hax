# Publishing

## OCaml

There is only the package `hax-engine`, that includes a binary and a
number of libraries.

We have no particular release procedure for the engine: we don't plan
on publishing it to opam.

## Rust

This repository is divided into several crates, some to be published,
some not. All crates should start with the `hax-` prefix, but
`cargo-hax` which is the entrypoint to the cargo `hax` subcommand.

Here is the list of the crates in this repository (excluding `tests`
and `examples`):

### cargo-hax

1. `hax-frontend-exporter-options` (`frontend/exporter/options`)
2. `hax-adt-into` (`frontend/exporter/adt-into`)
3. `hax-frontend-exporter` (`frontend/exporter`)
4. `hax-types` (`hax-types`)
5. `cargo-hax` (binaries) (`cli/cargo-hax`)
   - `cargo-hax`
   - `hax-export-json-schemas` (only with `--features legacy-engine`)

- `hax-driver` (`cli/driver`)
- `test-driver` (`cli/test-driver`)

### hax-lib

We publish the following crates that are helper libraries to be used
for hax code:

1. `hax-lib-macros-types` (`hax-lib/macros/types`)
2. `hax-lib-macros` (`hax-lib/macros`)
3. `hax-lib` (`hax-lib`)
4. `hax-bounded-integers` (`hax-bounded-integers`)

`cargo-hax` accepts only the `hax-lib` of its own version, so every `cargo-hax` release must publish a matching `hax-lib`, even for changes that only touch the binary.

### The Rust engine

1. `hax-rust-engine-macros` (`rust-engine/macros`)
2. `hax-rust-engine` (`rust-engine`)

### Crates that are not published

- `hax-engine-names` (`engine/names`) and
  `hax-engine-names-extract` (`engine/names/extract`): used only by
  the OCaml build of the engine.
- `hax-lib-protocol` (`hax-lib-protocol`) and
  `hax-lib-protocol-macros` (`hax-lib-protocol-macros`).

## Procedure
 1. Move the contents of `CHANGELOG.md` under the `[Unreleased]` section to a new section named following the target version. Commit this change.
 2. Bump the version number with `cargo release LEVEL --workspace --no-publish --no-tag --execute` (`cargo release --help` for more details on `LEVEL`, `cargo install cargo-release` if you don't already have this package). This will bump the version of every Rust crate, but also the version in `engine/dune-project`. This will also regenerate `engine/hax-engine.opam`. Note this will *not* publish the crate.
 3. Check that the default tool versions in `cli/cargo-hax/defaults.toml` are correct and that `cli/cargo-hax/tools-manifest.toml` lists them with checksums for every supported platform
 4. PR the change
 5. when the PR is merged in main, checkout `main` and run `cargo release --workspace --execute`

Note: for now, we are not publishing to Opam. Instead, let's just advertise the following for installation:
```bash
opam pin hax-engine https://github.com/hacspec/hax.git#the-release-tag
opam install hax-engine
```

## Notes
`cargo release` reads the `Cargo.toml` of each crates of the workspace.
Some creates are excluded from releasing: in their `Cargo.toml` manifest, they have `package.metadata.release.release` set to `false`.

Also, `cli/cargo-hax/Cargo.toml` specifies pre-release replacements for the engine: the version of the engine is bumped automatically by `cargo release`.
