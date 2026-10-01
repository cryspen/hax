---
authors:
  - tobias
title: "hax 0.4: easier to install and configure, and a new Lean backend"
date: 2026-09-29
---

We are happy to announce [hax 0.4](https://github.com/cryspen/hax/releases/tag/cargo-hax-v0.4.2). The release brings a one-command installation for the Lean backend, proof scenarios configured in a `hax.toml` file, a new Lean backend built on Aeneas, and new capabilities for the specification macros. This post walks through these highlights. The [changelog](https://github.com/cryspen/hax/blob/cargo-hax-v0.4.2/CHANGELOG.md) lists everything else, including many fixes and improvements to the engine, the proof libraries, and the core models.

## Installing hax

Until now, installing hax meant setting up an OCaml toolchain for the hax engine or using Nix or Docker. The new Lean backend does not use the hax engine. Instead, the `cargo-hax` command line tool drives [Charon](https://github.com/AeneasVerif/charon) and [Aeneas](https://github.com/AeneasVerif/aeneas), which translate Rust into Lean. Installing `cargo-hax` and a [Lean toolchain](https://lean-lang.org/install/) is therefore enough, given a C compiler and [rustup](https://rustup.rs/), which Charon uses at extraction time. hax 0.4 publishes `cargo-hax` as a pre-built binary for Linux (x86_64 and aarch64) and macOS (aarch64). The binary needs glibc 2.35 or newer on Linux, and macOS 11 or newer. With [cargo-binstall](https://github.com/cargo-bins/cargo-binstall) available, one command installs it:

```bash
cargo binstall cargo-hax
```

`cargo install --locked cargo-hax` builds the same binary from [crates.io](https://crates.io/crates/cargo-hax) and covers systems the pre-built binary does not support. Charon and Aeneas need no manual installation. hax downloads them on first use, verifies them against a manifest shipped with the release, and caches them.

`cargo-hax` and [`hax-lib`](https://crates.io/crates/hax-lib) are released together and must match. A 0.4.2 binary accepts only `hax-lib` 0.4.2 and otherwise aborts with instructions on how to resolve the mismatch.

The F\*, Rocq, ProVerif, and other backends still run through the hax engine and need the full installation via the setup script, Nix, or Docker, as described in the [README](https://github.com/cryspen/hax/blob/cargo-hax-v0.4.2/README.md#installation).

## Configuring a project

Before 0.4, a `cargo hax` invocation carried its configuration as flags: item selection, backend options, extra tool arguments. With 0.4, a project stores this configuration as proof scenarios in a `hax.toml` next to its `Cargo.toml`. The [barrett example](https://github.com/cryspen/hax/tree/cargo-hax-v0.4.2/examples/barrett)'s `hax.toml` declares two scenarios, one for Lean and one for F\*:

```toml
[scenario.barrett]
backend = "lean"

[scenario.barrett-fstar]
backend = "fstar"
z3rlimit = 100
```

`cargo hax extract` runs every scenario of the project, and `cargo hax extract barrett` runs a single scenario. Each scenario writes to `proofs/<scenario>/<backend>/`, so several extractions of one crate coexist. Scenarios support item selection (currently for the Lean backend only), cargo features, environment variables, and backend-specific options. The [manual](https://hax.cryspen.com/manual/tools/) documents the keys.

Charon, Aeneas, the Lean toolchain, and the hax Lean library have default versions shipped and tested with each hax release. Most projects should use these defaults. If needed, `hax.toml` can override them: `[tools]` pins Charon and Aeneas, while `[versions]` pins the Lean toolchain and the hax Lean library, which models Rust core. This is an advanced option: other combinations are untested and are your responsibility to maintain across hax releases.

The new `cargo hax tools` subcommands let you inspect the versions in use, install them ahead of time for CI or offline work, and clean the tool cache.

The hax version itself can be pinned alongside the `hax-lib` version in `Cargo.toml` with [cargo-run-bin](https://github.com/dustinblackman/cargo-run-bin):

```toml
[package.metadata.bin]
cargo-hax = { version = "0.4.2", bins = ["cargo-hax"], locked = true }
```

cargo-run-bin installs the pinned version on demand, and after `cargo bin --sync-aliases`, the usual `cargo hax` invocation uses that version.

Finally, `cargo hax` now exits with a non-zero status when an extraction fails. This lets a scenario run serve as a CI check, but CI scripts that relied on a zero exit status need adjusting. `cargo hax extract` followed by `git diff --exit-code` detects when the committed extraction output is out of date.

## The Lean/Aeneas backend

In the new Lean backend, Charon compiles Rust into an intermediate representation, and Aeneas translates it into pure functional Lean code. On top of this pipeline, hax extracts `hax_lib` pre- and postconditions as Lean specifications, provides the hax Lean library, and generates a complete Lean package that builds with `lake build`. The previous Lean backend, based on the hax engine, remains available as `legacy-lean`.

Take a slightly simplified version of the Barrett reduction from the barrett example:

```rust
#[hax_lib::requires((i64::from(value) >= -BARRETT_R && i64::from(value) <= BARRETT_R))]
#[hax_lib::ensures(|result| result > -FIELD_MODULUS && result < FIELD_MODULUS &&
                       result.rem_euclid(FIELD_MODULUS) == value.rem_euclid(FIELD_MODULUS))]
pub fn barrett_reduce(value: FieldElement) -> FieldElement {
    let t = i64::from(value) * BARRETT_MULTIPLIER;
    let t = t + (BARRETT_R >> 1);
    let quotient = t >> BARRETT_SHIFT;
    let quotient = quotient as i32;
    let sub = quotient * FIELD_MODULUS;
    value - sub
}
```

Running the `barrett` scenario turns the function into a definition in the `RustM` monad, which models failures such as panics and integer overflow. The `requires` and `ensures` attributes become `barrett_reduce.pre` and `barrett_reduce.post`, and hax combines them into a specification:

```lean
def barrett_reduce.spec (value : Std.I32) : Prop :=
  (barrett_reduce.pre value).holds →
  ⦃ ⌜ True ⌝ ⦄
  barrett_reduce value
  ⦃ ⇓ res => ⌜ (barrett_reduce.post value res).holds ⌝ ⦄
```

The `⦃ ... ⦄` brackets enclose a Hoare triple around the call, with a postcondition on the result `res`. The triple itself has the trivial precondition `True`, and the actual precondition is the implication in front of it. The specification states that, if the precondition holds, the function returns without failing and its result satisfies the postcondition.

hax also generates a theorem for this specification, whose proof is `sorry`, Lean's placeholder for a missing proof. The theorem lives in a `Verification` folder that hax never overwrites. The barrett example contains the finished proof, which uses the `hax_mvcgen` tactic and `grind`. The [Lean quick start](https://hax.cryspen.com/manual/lean/quick_start/) shows the workflow, the [Lean tutorial](https://hax.cryspen.com/manual/lean/tutorial/) walks through proving panic freedom and functional properties, and the [examples](https://github.com/cryspen/hax/tree/cargo-hax-v0.4.2/examples) in the repository provide larger cases.

## Specification updates

`hax_lib::ensures` takes the return value by value, which does not work for non-Copy types. hax 0.4 adds `hax_lib::ensures_ref`, which takes it by reference:

```rust
#[hax_lib::ensures_ref(|result| result.len() == 2)]
pub fn pair(x: u64) -> Vec<u64> {
    vec![x, x]
}
```

`requires` and `ensures` now also work under `cfg_attr` in impl blocks and on methods whose signatures mention associated types. Cases that are still unsupported produce an explicit error instead of silently dropping the specification.

hax can now extract specifications written with [anodized](https://github.com/mkovaxx/anodized), a crate that aims to provide one specification syntax for several Rust verification tools. hax extracts anodized's `#[spec(requires: .., maintains: .., ensures: ..)]` attributes as pre- and postconditions, where a `maintains` clause becomes both. `hax_lib::requires` and `hax_lib::ensures` remain the recommended way to write specifications for hax. The [anodized example](https://github.com/cryspen/hax/tree/cargo-hax-v0.4.2/examples/anodized) shows both side by side.

## Thanks and what's next

Thanks to everyone who contributed to this release:

* [Alexandre Baldé](https://github.com/rockbmb)
* [Benjamin A. Beasley](https://github.com/musicinmybrain)
* [Alexander Bentkamp](https://github.com/abentkamp)
* [Karthikeyan Bhargavan](https://github.com/karthikbhargavan)
* [Clément Blaudeau](https://github.com/clementblaudeau)
* [Nikolay Bryskin](https://github.com/nikicat)
* [Maxime Buyse](https://github.com/maximebuyse)
* [@edouardparis](https://github.com/edouardparis)
* Frantisek Farka
* [Lucas Franceschino](https://github.com/W95Psp)
* [Cory Francis Myers](https://github.com/cfm)
* [Onyeka Obi](https://github.com/MavenRain)
* [William Takeshi Pereira](https://github.com/WilliamTakeshi)
* [Tobias Reiher](https://github.com/treiher)
* [@rocodes](https://github.com/rocodes)

Our main goal for the next release is robustness. We want hax to work on almost any crate with all backends. We will expand our test suite to track progress towards this goal. We also plan to improve proof ergonomics, making it easier to go from an extraction to a finished proof.

As always, bug reports and questions are welcome on the [issue tracker](https://github.com/cryspen/hax/issues) and on [Zulip](https://hacspec.zulipchat.com).
