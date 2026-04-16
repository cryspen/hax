#!/usr/bin/env bash
#
# Downloads pre-built aeneas and charon binaries at the versions pinned
# by this repository.  Installs them into ~/.cargo/bin/ (the same place
# cargo-hax lives).
#
# Requirements: curl, tar

set -euo pipefail

SCRIPTPATH="$(cd -- "$(dirname "$0")" >/dev/null 2>&1; pwd -P)"

# ---------- helpers ----------------------------------------------------------

die() { printf '\e[31mError: %s\e[0m\n' "$*" >&2; exit 1; }
warn() { printf '\e[33mWarning: %s\e[0m\n' "$*" >&2; }
info() { printf '\e[34m%s\e[0m\n' "$*"; }

# Read a pin file: strip comments and blank lines, return the first
# non-empty line.
read_pin() {
    local pin_file="$1"
    [ -f "$pin_file" ] || die "Pin file not found: $pin_file"
    grep -v '^#' "$pin_file" | grep -v '^$' | head -1
}

# Read a keyed value from a pin file.  Lines have the form "key value".
read_pin_key() {
    local pin_file="$1" key="$2"
    grep -v '^#' "$pin_file" | grep "^${key} " | head -1 | cut -d' ' -f2-
}

# ---------- detect platform --------------------------------------------------

OS="$(uname -s)"
ARCH="$(uname -m)"

case "$OS" in
    Linux)  os_tag="linux" ;;
    Darwin) os_tag="macos" ;;
    *)      die "Unsupported OS: $OS" ;;
esac

case "$ARCH" in
    x86_64)  arch_tag="x86_64" ;;
    aarch64|arm64) arch_tag="aarch64" ;;
    *)       die "Unsupported architecture: $ARCH" ;;
esac

PLATFORM="${os_tag}-${arch_tag}"

# ---------- read pins --------------------------------------------------------

AENEAS_TAG="$(read_pin "$SCRIPTPATH/aeneas-pin")"
CHARON_TAG="$(read_pin "$SCRIPTPATH/charon-pin")"

# Expected versions: aeneas reports a commit SHA prefix, charon reports semver.
# The aeneas SHA is extracted from the release tag; the charon version is
# stored explicitly in charon-pin as "version X.Y.Z".
AENEAS_EXPECTED_SHA=$(echo "$AENEAS_TAG" | sed 's/.*-//' | cut -c1-8)
CHARON_EXPECTED_VERSION=$(read_pin_key "$SCRIPTPATH/charon-pin" "version")

# ---------- check if already installed at the right version ------------------

check_aeneas_version() {
    local bin="$1"
    # `aeneas -version` outputs "aeneas <sha-prefix>"
    local actual
    actual=$("$bin" -version 2>/dev/null | awk '{print $2}' | cut -c1-8) || return 1
    [ "$actual" = "$AENEAS_EXPECTED_SHA" ]
}

check_charon_version() {
    local bin="$1"
    # `charon version` outputs a semver string like "0.1.174"
    local actual
    actual=$("$bin" version 2>/dev/null) || return 1
    [ -z "$CHARON_EXPECTED_VERSION" ] || [ "$actual" = "$CHARON_EXPECTED_VERSION" ]
}

AENEAS_FOUND=$(command -v aeneas 2>/dev/null || true)
CHARON_FOUND=$(command -v charon 2>/dev/null || true)

if [ -n "$AENEAS_FOUND" ] && [ -n "$CHARON_FOUND" ]; then
    AENEAS_OK=false
    CHARON_OK=false
    check_aeneas_version "$AENEAS_FOUND" && AENEAS_OK=true
    check_charon_version "$CHARON_FOUND" && CHARON_OK=true

    if [ "$AENEAS_OK" = true ] && [ "$CHARON_OK" = true ]; then
        info "aeneas found at $AENEAS_FOUND (version matches pin)"
        info "charon found at $CHARON_FOUND (version matches pin)"
        info "Both binaries are already installed at the correct version, skipping download."
        exit 0
    fi

    if [ "$AENEAS_OK" = false ]; then
        printf '\e[31mError: aeneas found at %s but version does not match pin (expected %s)\e[0m\n' "$AENEAS_FOUND" "$AENEAS_EXPECTED_SHA" >&2
    fi
    if [ "$CHARON_OK" = false ]; then
        printf '\e[31mError: charon found at %s but version does not match pin (expected %s)\e[0m\n' "$CHARON_FOUND" "$CHARON_EXPECTED_VERSION" >&2
    fi
    die "Remove the existing binaries or update them to the pinned versions."
fi

# ---------- download & install -----------------------------------------------

info "Pinned versions:"
info "  aeneas: $AENEAS_TAG"
info "  charon: $CHARON_TAG"
info "  platform: $PLATFORM"

INSTALL_DIR="${CARGO_HOME:-$HOME/.cargo}/bin"
mkdir -p "$INSTALL_DIR"

AENEAS_URL="https://github.com/AeneasVerif/aeneas/releases/download/${AENEAS_TAG}/aeneas-${PLATFORM}.tar.gz"
CHARON_URL="https://github.com/AeneasVerif/charon/releases/download/${CHARON_TAG}/charon-${PLATFORM}.tar.gz"

TMPDIR="$(mktemp -d)"
trap 'chmod -R u+w "$TMPDIR" 2>/dev/null; rm -rf "$TMPDIR"' EXIT

download_and_extract() {
    local name="$1" url="$2"
    info "Downloading $name from $url ..."
    local archive="$TMPDIR/${name}.tar.gz"
    curl -fSL --retry 3 -o "$archive" "$url" \
        || die "Failed to download $name. Check that the release tag and platform exist."
    mkdir -p "$TMPDIR/$name"
    tar -xzf "$archive" -C "$TMPDIR/$name"
}

download_and_extract "aeneas" "$AENEAS_URL"
download_and_extract "charon" "$CHARON_URL"

install_bin() {
    local src="$1" dst="$INSTALL_DIR/$(basename "$1")"
    cp -f "$src" "$dst"
    chmod +x "$dst"
    info "  installed $(basename "$dst")"
}

info "Installing to $INSTALL_DIR ..."
install_bin "$TMPDIR/aeneas/aeneas"
install_bin "$TMPDIR/charon/charon"
install_bin "$TMPDIR/charon/charon-driver"

# ---------- smoke test -------------------------------------------------------

info ""
if "$INSTALL_DIR/aeneas" -version >/dev/null 2>&1; then
    info "aeneas: OK"
else
    die "aeneas smoke test failed"
fi

if "$INSTALL_DIR/charon" version >/dev/null 2>&1; then
    info "charon: OK"
else
    die "charon smoke test failed"
fi

info ""
info "Done! aeneas and charon are installed in $INSTALL_DIR"
info "You can now run: cargo hax into aeneas-lean"
