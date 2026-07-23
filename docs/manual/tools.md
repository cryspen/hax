---
weight: 100
---

# Managing tool versions

Some hax backends rely on external tools. The `lean` backend (`cargo hax into lean`) runs the [aeneas](https://github.com/AeneasVerif/aeneas) pipeline, which needs the `aeneas` and `charon` binaries. hax manages these binaries for you: it knows which versions a project needs, downloads pre-built binaries on demand, verifies them against a manifest shipped with the release, and caches them so later runs reuse them.

This page covers the `cargo hax tools` subcommands, the `hax.toml` file that pins versions per project, how a version is resolved, and how to point hax at a locally built binary instead.

## Managed and declared tools

hax distinguishes two kinds of tool version.

*Managed tools* are installed by hax. There are two: `aeneas` and `charon`. hax downloads, verifies, and caches these binaries itself.

*Declared versions* are versions hax must know but does not install. There are two: `lean` (the Lean toolchain, written verbatim into the `lean-toolchain` files hax generates) and `hax-lean-lib` (the Lean library that extracted code builds against).

Every release of hax ships with a built-in default for each of these, tested against that release. You only need to configure anything when you want to deviate from those defaults.

## On-demand installation and the cache

You do not have to install anything up front. The first time a `cargo hax into lean` run needs `aeneas` or `charon`, hax downloads the resolved version, verifies its SHA-256 checksum against the shipped manifest, and stores it in a cache. Subsequent runs reuse the cached binary.

The cache lives under `$XDG_CACHE_HOME/hax/tools/` (falling back to `~/.cache/hax/tools/` when `XDG_CACHE_HOME` is unset), with one directory per tool and version. Downloads are verified before they are moved into place, so an interrupted download never leaves a half-installed version behind.

## The `cargo hax tools` subcommands

### `tools show`

`cargo hax tools show` reports, for the current project, which version of each tool is active and where that choice comes from (an environment override, a `hax.toml` entry, or the built-in default). It also reports the `hax-lib` version in scope and its compatibility with your `cargo-hax`. Run it inside your project to understand what a run would use without triggering any download.

```bash
cargo hax tools show
```

When a member crate of a workspace overrides a version, `show` lists the differing entries under that crate.

### `tools install`

`cargo hax tools install`, run inside a project, downloads and caches everything that project resolves to (the union across all workspace crates: workspace pins, per-member overrides, and defaults). This is what you want in CI, or before going offline, so the later extraction run does not have to download anything.

```bash
cargo hax tools install
```

Tools pinned to a local `path` are skipped with a note, since they are provided outside the cache. Environment overrides are ignored here: `install` populates the cache for the committed configuration.

You can also install one specific version into the machine-wide cache, from any directory, without a project:

```bash
cargo hax tools install charon@nightly-2026.07.01
```

A cached version is reused as-is. Pass `--force` to re-download and re-verify it instead. A version unknown to this release's manifest still installs, but without checksum verification and with a warning; `--force` is how you later obtain a verified copy, by reinstalling once a cargo-hax release ships a checksum for that version.

```bash
cargo hax tools install charon@nightly-2026.07.01 --force
```

### `tools list`

`cargo hax tools list` shows the versions this release can install with checksum verification, as recorded in the manifest, marking the ones already in your cache. It works outside a project.

```bash
cargo hax tools list              # all managed tools
cargo hax tools list charon       # one tool
cargo hax tools list --installed  # only versions present in the cache
cargo hax tools list --all        # every version, not just the most recent
```

Cached versions are always listed, even ones absent from this release's manifest. Each version is annotated in parentheses:

- `default`: the version this release resolves to when a project pins nothing.
- `installed`: present in the local cache.
- `unverified`: the cached copy was installed without checksum verification (through the fallback path); once a release ships a checksum for it, reinstall with `--force` to verify it.
- `not in manifest`: the version is not in this release's manifest, so it can only be reinstalled through the unverified fallback path.

## Pinning versions with `hax.toml`

To pin versions for a project, commit a `hax.toml` at the workspace root. It has two tables.

```toml
[tools]
# Managed tools, pinned by upstream release tag.
aeneas = "nightly-2026.07.01"
charon = "nightly-2026.07.01"

[versions]
# Declared-only versions.
lean = "leanprover/lean4:v4.30.0-rc2"
hax-lean-lib = "v0.1.0"
```

A `[tools]` entry is either a version string, as above, or a table. The table form mirrors Cargo's dependency syntax and must declare exactly one of `version` or `path`:

```toml
[tools]
aeneas = { version = "nightly-2026.07.01" }
charon = { path = "vendor/bin/charon" }
```

A `path` points at an existing executable and is used as-is (see [Using a local build](#using-a-local-build) below). A relative path is resolved against the directory of the `hax.toml` that declares it.

Entries for tools or `[versions]` keys that a given hax release does not know are warned about and ignored, so a `hax.toml` written for a newer hax stays readable by an older one. A malformed entry (for example one declaring both `version` and `path`) is an error.

### Per-crate overrides

In a workspace, a member crate may carry its own `hax.toml` that overrides the workspace-root one for that crate. hax reads `hax.toml` from the workspace root and from member-crate roots only. A `hax.toml` sitting elsewhere is reported as a stray file and has no effect.

## How a version is resolved

For a given crate, hax resolves each tool through the following order, highest precedence first:

1. the `HAX_<TOOL>_BINARY` environment variable (managed tools only),
2. the entry in the member crate's `hax.toml`,
3. the entry in the workspace-root `hax.toml`,
4. the built-in default shipped with this hax release.

Declared `[versions]` entries resolve through levels 2 to 4 of the same order; they have no environment override.

Whenever a run resolves a managed tool to something other than the built-in default, hax prints a one-line notice naming the version this release was tested with.

## Using a local build

If you build `aeneas` or `charon` yourself (for example from source), point hax at your binary in one of two ways.

Set the `HAX_AENEAS_BINARY` or `HAX_CHARON_BINARY` environment variable to the path of the executable, or commit a `path` entry in `hax.toml`:

```toml
[tools]
charon = { path = "vendor/bin/charon" }
```

A path or environment override points at the executable whose name matches the tool. When a tool comprises several executables, the others must sit next to it: `charon` and `charon-driver` must be in the same directory, and a missing sibling is reported as an error naming the file hax expected.

## The `hax-lib` compatibility check

`cargo-hax` and `hax-lib` are released together under one version number. Before processing a crate, hax checks that the crate's direct `hax-lib` dependency is one this `cargo-hax` binary understands: the accepted range is the binary's own version series, capped at its own version (for example a 0.3.7 binary accepts `hax-lib >=0.3.0, <=0.3.7`). A crate with no direct `hax-lib` dependency is not checked.

If the check fails, hax aborts before running any tool and prints the mismatch with a remedy:

- when the found `hax-lib` is newer than the binary (typically after a `cargo update`), update `cargo-hax` to the matching release, or pin the `hax-lib` dependency back to the binary's version in `Cargo.toml`;
- when it is older or on a different series, update the `hax-lib` dependency in `Cargo.toml`, or install a `cargo-hax` compatible with that `hax-lib`.

The `tools` subcommands never abort on this check: `cargo hax tools show` reports the compatibility instead of failing, and `cargo hax tools install` ignores it.
