---
weight: 100
---

# Managing tool versions

Some hax backends rely on external tools. The `lean` backend (`cargo hax into lean`) runs the [aeneas](https://github.com/AeneasVerif/aeneas) pipeline, which needs the `aeneas` and `charon` binaries. hax manages these binaries for you: it knows which versions a project needs, downloads pre-built binaries on demand, verifies them against a manifest shipped with the release, and caches them so later runs reuse them.

This page covers the `cargo hax tools` subcommands, the `hax.toml` file that pins versions per project, how a version is resolved, and how to point hax at a locally built binary instead.

Using the default versions shipped with your hax release is the recommended way to work: they are tested together, and nothing has to be configured for them. Pinning versions individually is an advanced option for when the defaults do not work for your project. Combinations other than the defaults are untested, and establishing that one works, and keeps working across hax releases, is up to you.

## Managed and declared tools

hax distinguishes two kinds of tool version.

*Managed tools* are installed by hax. There are two: `aeneas` and `charon`. hax downloads, verifies, and caches these binaries itself.

*Declared versions* are versions hax must know but does not install. There are two: `lean` (the Lean toolchain, written verbatim into the `lean-toolchain` files hax generates) and `hax-lean-lib` (the Lean library that extracted code builds against).

Every release of hax ships with a built-in default for each of these, tested together as a set. You only need to configure anything when you want to deviate from those defaults.

## On-demand installation and the cache

You do not have to install anything up front. The first time a `cargo hax into lean` run needs `aeneas` or `charon`, hax downloads the resolved version, verifies its SHA-256 checksum against the shipped manifest, and stores it in a cache. Subsequent runs reuse the cached binary.

The cache lives under `$XDG_CACHE_HOME/hax/tools/` (falling back to `~/.cache/hax/tools/` when `XDG_CACHE_HOME` is unset, empty, or not an absolute path), with one directory per tool and version. Downloads are verified before they are moved into place, so an interrupted download never leaves a half-installed version behind. They use the proxy and the certificate store the environment configures. The cache only grows; drop versions you no longer need with [`tools remove`](#tools-remove), or all of them with [`tools clean`](#tools-clean).

Pre-built binaries are available for the platforms hax supports: Linux (`x86_64` and `aarch64`) and macOS (`aarch64`). On any other platform there is nothing to download, and hax reports so, naming the version it wanted; build `aeneas` and `charon` yourself and point hax at them as described under [Using a local build](#using-a-local-build).

## The `cargo hax tools` subcommands

### `tools show`

`cargo hax tools show` reports, for the current project, which version of each tool is active and where that choice comes from (a `hax.toml` entry or the built-in default). It also reports the `hax-lib` version in scope and its compatibility with your `cargo-hax`. Run it inside your project to understand what a run would use without triggering any download.

```bash
cargo hax tools show
```

When a member crate of a workspace overrides a version, `show` lists the differing entries under that crate.

### `tools pin`

`cargo hax tools pin` writes version pins into the current project's `hax.toml`, creating the file if it does not exist.

```bash
cargo hax tools pin                                # pin this release's defaults
cargo hax tools pin charon@nightly-2026.07.01      # set one managed tool
cargo hax tools pin lean@leanprover/lean4:v4.31.0  # set one declared version
```

Without an argument, `pin` writes the built-in default version of every managed tool and declared version, freezing what this release resolves to. Run it again after upgrading hax to move the pins forward. With a `<name>@<version>` argument, it sets that one entry: managed tools go to `[tools]`, declared versions to `[versions]`. A version this release's manifest does not know is written anyway, with a warning that installing it will go through the unverified fallback.

Editing preserves the rest of the file: formatting, comments, and entries `pin` does not know. A tool pinned to a `path` is reported and left alone, since `pin` writes version entries only. Pointing a tool at a [local build](#using-a-local-build), and unpinning one, are done by hand.

Inside a member crate of a workspace, `pin` writes that crate's own `hax.toml`, creating a [per-crate override](#per-crate-overrides) and warning that it does. Anywhere else it writes the workspace root's.

### `tools install`

`cargo hax tools install`, run inside a project, downloads and caches everything that project resolves to (the union across all workspace crates: workspace pins, per-member overrides, and defaults). This is what you want in CI, or before going offline, so the later extraction run does not have to download anything.

```bash
cargo hax tools install
```

Tools pinned to a local `path` are skipped with a note, since they are provided outside the cache.

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

### `tools remove`

`cargo hax tools remove` deletes one version from the machine-wide cache. Like `install <tool>@<version>`, it works from any directory.

```bash
cargo hax tools remove charon@nightly-2026.07.01
```

Removal is always safe: a later run that needs the version downloads it again. Deleting version directories, or the whole cache, by hand is equally safe.

### `tools clean`

`cargo hax tools clean` deletes the entire tool cache: every cached version of every tool. It works from any directory and reports how many versions it removed.

```bash
cargo hax tools clean
```

## Pinning versions with `hax.toml`

Pinning versions is an advanced option, only needed when the defaults do not work for your project. hax neither checks nor guarantees that a pinned combination of `aeneas`, `charon`, Lean toolchain, and Lean library versions works together; testing that is your responsibility, including after upgrading hax.

To pin versions for a project, commit a `hax.toml` at the workspace root. It has two tables. [`tools pin`](#tools-pin) writes this file for you.

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

A `[tools]` version names a release tag of the tool's upstream repository, which is where hax fetches the binaries from; it may consist of ASCII alphanumerics and `.-_+:` (it also names the tool's directory in the cache). A tag hax has no artifact for is reported when the install is attempted.

A `path` points at an existing executable and is used as-is (see [Using a local build](#using-a-local-build) below). A relative path is resolved against the directory of the `hax.toml` that declares it.

A `[versions]` value is a version, tag, or toolchain name of ASCII alphanumerics and `.-_+:/`. Anything else is rejected: these values end up in the files hax generates for a Lean project, and the restriction keeps them from being anything but a version there.

Entries for tools or `[versions]` keys that a given hax release does not know are warned about and ignored, so a `hax.toml` written for a newer hax stays readable by an older one. A malformed entry (for example one declaring both `version` and `path`) is an error.

Besides the two tables, a top-level `project-files` key (a boolean, default `true`) governs whether hax generates and checks the proof-project files around an extraction, for every backend that has them (currently the Lean package). Set `project-files = false` to manage these files yourself; hax then also skips the pin and root-module checks described below. The extraction directory itself, the `Extraction.lean` module importing it, and the wiring of external definitions to `Assumptions/` are extraction behavior, not project files: hax keeps clearing and rewriting the first two and maintaining the third. With the key set to `false`, the lakefile, the toolchain file, and the root module are yours to create and to keep in sync with the resolved versions; hax no longer warns when they drift.

### Per-crate overrides

In a workspace, a member crate may carry its own `hax.toml` that overrides the workspace-root one for that crate. hax reads `hax.toml` from the workspace root and from member-crate roots only. A `hax.toml` sitting elsewhere is reported as a stray file and has no effect.

## How a version is resolved

For a given crate, hax resolves each tool through the following order, highest precedence first:

1. the entry in the member crate's `hax.toml`,
2. the entry in the workspace-root `hax.toml`,
3. the built-in default shipped with this hax release.

Declared `[versions]` entries resolve through the same order.

Whenever a run resolves a managed tool or a declared version to something other than the built-in default, hax prints a one-line notice naming the version this release was tested with.

## Using a local build

If you build `aeneas` or `charon` yourself (for example from source), commit a `path` entry for it in `hax.toml` instead of a version:

```toml
[tools]
charon = { path = "vendor/bin/charon" }
```

A relative path is resolved against the directory of the `hax.toml` declaring it. The entry points at the executable whose name matches the tool. When a tool comprises several executables, the others must sit next to it: `charon` and `charon-driver` must be in the same directory, and a missing sibling is reported as an error naming the file hax expected.

## The `hax-lib` compatibility check

`cargo-hax` and `hax-lib` are released together under one version number, and that pair is the only combination that is tested. Before processing a crate, hax checks that the crate's direct `hax-lib` dependency matches the binary's own version exactly (a 0.3.7 binary accepts only `hax-lib` 0.3.7). A crate with no direct `hax-lib` dependency is not checked, and neither are workspace members this run does not process. When the run selects packages itself (`-C -p <PKG> ;`, `-C --workspace ;`), hax leaves that selection to Cargo and aborts only on an incompatibility no selection can avoid, that is one shared by every member of the workspace; a workspace mixing compatible and incompatible `hax-lib` versions fails at compile time instead.

If the check fails, hax aborts before running any tool and prints the mismatch with a remedy:

- when the found `hax-lib` is newer than the binary (typically after a `cargo update`), update `cargo-hax` to the matching release, or pin the `hax-lib` dependency back to the binary's version in `Cargo.toml`;
- when it is older, update the `hax-lib` dependency (for example `cargo update -p hax-lib --precise <version>`), or install the `cargo-hax` matching that `hax-lib`.

The `tools` subcommands never abort on this check: `cargo hax tools show` reports the compatibility instead of failing, and `cargo hax tools install` ignores it.

## The Lean root module check

The root module `<PkgName>.lean` is generated once, then left to you: regenerating it would overwrite your edits. Its generated imports are stable: the extracted modules are reached through `<PkgName>/Extraction.lean`, which hax rewrites on every extraction, so files the extraction adds or drops never require a root-module edit. On every Lean extraction, hax warns when the root module imports neither `<PkgName>.Extraction` nor its commented-out form (the extraction would silently stay out of the build), likewise for the `Verification/ProofObligations.lean` stub, and when an import under `<PkgName>.Extraction.` names a file the extraction no longer produces (say, in a root module predating `Extraction.lean`), which fails the build less legibly than a warning here. The fix is editing the import line by hand. A commented-out import (`-- import ...`) silences the warnings for that module, and for the `Verification/` stub it also stops hax from recreating it. `Extraction.lean` skips the `Extraction/ProofObligations.lean` template: it is the starting point for the proofs in `Verification/ProofObligations.lean`, and importing both would declare every obligation twice.

## The Lean project pin check

The Lean package files hax generates (`lakefile.toml`, `lean-toolchain`) are never overwritten, so their pinned versions can fall behind after a hax upgrade or a `hax.toml` change. On every Lean extraction, hax compares an existing lakefile's `aeneas` and `Hax` revisions and the `lean-toolchain` contents against the currently resolved versions, and warns about each pin that differs: update the pin, or delete the file and re-run to regenerate it. Requires hax does not manage are left alone, as is the `aeneas` pin when the binary comes from a `path` entry, which names no version to compare against.
