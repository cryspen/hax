# Publishing

## OCaml

The OCaml engine is a single package, `hax-engine`, with a binary and a number of libraries. It is not published to opam and has no release step of its own.

## Rust

All crates start with the `hax-` prefix, except `cargo-hax` (the entrypoint to the cargo `hax` subcommand) and `test-driver`. The published crates, in dependency order:

**cargo-hax**

1. `hax-frontend-exporter-options` (`frontend/exporter/options`)
2. `hax-adt-into` (`frontend/exporter/adt-into`)
3. `hax-frontend-exporter` (`frontend/exporter`)
4. `hax-types` (`hax-types`)
5. `cargo-hax` (`cli/cargo-hax`)
6. `hax-driver` (`cli/driver`)
7. `test-driver` (`cli/test-driver`)

**hax-lib**

1. `hax-lib-macros-types` (`hax-lib/macros/types`)
2. `hax-lib-macros` (`hax-lib/macros`)
3. `hax-lib` (`hax-lib`)
4. `hax-bounded-integers` (`hax-bounded-integers`)

`cargo-hax` accepts only the `hax-lib` of its own version, so every `cargo-hax` release must publish a matching `hax-lib`, even for changes that only touch the binary.

**Rust engine**

1. `hax-rust-engine-macros` (`rust-engine/macros`)
2. `hax-rust-engine` (`rust-engine`)

Crates with `package.metadata.release.release = false` in their `Cargo.toml` are not published: `hax-engine-names` and `hax-engine-names-extract` (used only by the OCaml build of the engine), `hax-lib-protocol` and `hax-lib-protocol-macros`.

## Binaries

Pushing the release's `cargo-hax-v*` tag runs the `release` workflow, which attaches a `cargo-hax` binary per supported platform to the GitHub release it creates at that tag. `cargo binstall cargo-hax` downloads those, at the names `package.metadata.binstall` in `cli/cargo-hax/Cargo.toml` declares, so both the archives and the published manifest have to be in place for a version to be binstallable. The `binstall` workflow verifies that pairing at the end of every `release` run; a manual dispatch re-checks a released version at any time.

## Procedure

1. Bump the version number with `cargo release LEVEL --workspace --no-publish --no-tag --execute` (`cargo install cargo-release` if needed). This bumps the version of every Rust crate and the version in `engine/dune-project`, regenerates `engine/hax-engine.opam`, and renames the `[Unreleased]` section of `CHANGELOG.md` to the target version. It does not publish anything.
2. Work through the pre-merge checklist in the PR's description.
3. PR the change.
4. When the PR is merged, checkout `main` and run the `cargo release` steps `publish`, `tag` and `push`, each with `--workspace --execute`. The one-shot `cargo release --workspace --execute` does not work here: it re-applies the pre-release replacements, which fail once the changelog is rotated.
5. Check that the `release` workflow went through. It attaches a `cargo-hax` archive per platform to the GitHub release at the `cargo-hax-v*` tag, then installs the released version with `cargo binstall` on every platform. GitHub raises push events for only some tags of a multi-tag push: when no run started, dispatch the workflow with `gh workflow run release.yml --ref cargo-hax-vX.Y.Z` (or the "Run workflow" button under Actions, picking the tag as the ref). The tag must be the ref: a dispatch on any other ref is recognized as not being a release and skipped.
