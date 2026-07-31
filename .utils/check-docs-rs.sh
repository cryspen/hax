#!/usr/bin/env bash

# Builds the documentation of a crate of this workspace exactly the way docs.rs
# does, and fails whenever docs.rs would fail. See issue #2087: the docs of
# `hax-lib` failed to build on docs.rs while building just fine locally.
#
# Running `cargo doc` in this repository is not enough to catch such issues:
#  - docs.rs honors the `[package.metadata."docs.rs"]` table of the crate (extra
#    `--cfg`s, features, ...). The binary `cargo-docs-rs` (from the crate
#    `cargo-docs-rs`) replays the very command docs.rs runs;
#  - docs.rs builds the *packaged* crate, in isolation, so the
#    `.cargo/config.toml` of this repository (which sets `--cfg hax` for every
#    build) doesn't apply. This script thus packages the crate and unpacks it
#    outside of this workspace.
#
# Usage: ./.utils/check-docs-rs.sh [CRATE]
# The toolchain can be overridden with the environment variable
# `DOCS_RS_TOOLCHAIN` (defaults to the channel pinned in `rust-toolchain.toml`).

set -euo pipefail

CRATE="${1:-hax-lib}"

cd "$(git rev-parse --show-toplevel)"
REPO="$PWD"

for binary in jq cargo-docs-rs; do
    command -v "$binary" > /dev/null || {
        >&2 echo "This script requires '$binary' to be in PATH."
        >&2 echo "  → 'cargo-docs-rs' can be installed with 'cargo install cargo-docs-rs'"
        exit 1
    }
done

# docs.rs runs on nightly: use the nightly this repository pins.
TOOLCHAIN="${DOCS_RS_TOOLCHAIN:-$(sed -n 's/^channel *= *"\(.*\)"/\1/p' rust-toolchain.toml)}"
# Always give the toolchain explicitly: this makes `rustup` ignore
# `rust-toolchain.toml`, whose (heavy) components are useless here.
cargo() { command cargo "+$TOOLCHAIN" "$@"; }

METADATA="$(cargo metadata --format-version 1 --no-deps)"
VERSION="$(jq -r --arg c "$CRATE" '.packages[] | select(.name == $c) | .version' <<< "$METADATA")"
[[ -n "$VERSION" ]] || { >&2 echo "No crate '$CRATE' in this workspace."; exit 1; }

echo "> Packaging $CRATE v$VERSION"
cargo package -p "$CRATE" --no-verify --allow-dirty

WORKDIR="$(mktemp -d)"
trap 'rm -rf "$WORKDIR"' EXIT
tar xzf "target/package/$CRATE-$VERSION.crate" -C "$WORKDIR"
cd "$WORKDIR/$CRATE-$VERSION"

# The packaged crate depends on the *published* versions of the other crates of
# this workspace: patch those in, so that we check the current sources.
{
    echo ""
    echo "[patch.crates-io]"
    jq -r --arg c "$CRATE" '
      (.packages | map({key: .name, value: (.manifest_path | rtrimstr("/Cargo.toml"))}) | from_entries) as $members
      | .packages[] | select(.name == $c) | .dependencies[].name
      | select(in($members))
      | "\(.) = { path = \"\($members[.])\" }"
    ' <<< "$METADATA" | sort -u
} >> Cargo.toml

echo "> Building the documentation of $CRATE as docs.rs would"
cargo docs-rs
