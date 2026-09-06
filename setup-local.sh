#!/usr/bin/env bash
#
# Installs the matched cargo-hax + hax-engine binaries into a specific
# opam switch's bin dir instead of the global ~/.cargo/bin. Pairing the
# Rust and OCaml binaries in one switch keeps their embedded version
# strings in sync, which the runtime version check requires, and lets
# different switches hold different hax versions at once.
#
# Usage:
#     ./setup-local.sh                       # installs into $HAX_OPAM_SWITCH (default: hax)
#     HAX_OPAM_SWITCH=hax ./setup-local.sh   # explicit
#
# Idempotent: re-running just rebuilds + reinstalls.

set -euo pipefail

HAX_OPAM_SWITCH="${HAX_OPAM_SWITCH:-hax}"
OPAM_JOBS="${OPAM_JOBS:-4}"
INSTALL_ROOT="$HOME/.opam/$HAX_OPAM_SWITCH"

REPO_ROOT="$(cd -- "$(dirname "$0")" >/dev/null 2>&1 ; pwd -P)"
cd "$REPO_ROOT"

# Sanity checks
if [ ! -d "$INSTALL_ROOT" ]; then
    echo "Error: opam switch '$HAX_OPAM_SWITCH' does not exist at $INSTALL_ROOT" >&2
    echo "Create it first: opam switch create $HAX_OPAM_SWITCH 5.4.1" >&2
    exit 1
fi
for bin in opam node rustup jq; do
    command -v "$bin" >/dev/null 2>&1 || { echo "Error: '$bin' not in PATH" >&2; exit 1; }
done

echo "[setup-local] HAX repo:   $REPO_ROOT"
echo "[setup-local] opam switch: $HAX_OPAM_SWITCH"
echo "[setup-local] cargo --root: $INSTALL_ROOT"
echo "[setup-local] git rev:     $(git -C "$REPO_ROOT" rev-parse --short HEAD)"

# engine/names/extract's build.rs shells out to cargo-hax (via
# HAX_CARGO_COMMAND_PATH, else a bare cargo-hax on PATH) and rejects a
# version mismatch, so point it at the switch's own binaries.
export PATH="$INSTALL_ROOT/bin:$PATH"
export HAX_CARGO_COMMAND_PATH="$INSTALL_ROOT/bin/cargo-hax"

# 1. Install the Rust binaries into the switch's bin, reusing the
#    workspace's canonical crate list and per-crate features.
source "$REPO_ROOT/.utils/install-rust-binaries.sh"
install_rust_binaries --force --root "$INSTALL_ROOT"

# 2. Install hax-engine via opam, pinned to this repo's engine/ dir
{
    export OPAMJOBS="$OPAM_JOBS"
    export OCAMLRUNPARAM="o=20"
    export OPAMERRLOGLEN=0
    # macOS opam can't detect node via brew sometimes
    export OPAMASSUMEDEPEXTS=1
}

# opam installs hax-engine read-only; drop any stale copy so the reinstall
# can write the new binary instead of failing to overwrite it.
rm -f "$INSTALL_ROOT/bin/hax-engine"

# Pin engine to THIS checkout (re-pinning is fine; opam will update)
opam pin add --switch="$HAX_OPAM_SWITCH" --yes --kind=path \
    hax-engine "$REPO_ROOT/engine"

# Re-install to pick up any source changes
opam reinstall --switch="$HAX_OPAM_SWITCH" --yes --assume-depexts hax-engine || \
    opam install --switch="$HAX_OPAM_SWITCH" --yes --assume-depexts hax-engine

echo ""
echo "[setup-local] done."
echo ""
echo "To use this hax: eval \$(opam env --switch=$HAX_OPAM_SWITCH)"
echo "Verify match:    cargo-hax --version  &&  ls -l \$(which hax-engine)"
