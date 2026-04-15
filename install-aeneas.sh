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
info() { printf '\e[34m%s\e[0m\n' "$*"; }

# Read a pin file: strip comments and blank lines, return the first
# non-empty line.
read_pin() {
    local pin_file="$1"
    [ -f "$pin_file" ] || die "Pin file not found: $pin_file"
    grep -v '^#' "$pin_file" | grep -v '^$' | head -1
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

info "Pinned versions:"
info "  aeneas: $AENEAS_TAG"
info "  charon: $CHARON_TAG"
info "  platform: $PLATFORM"

# ---------- install directory ------------------------------------------------

INSTALL_DIR="${CARGO_HOME:-$HOME/.cargo}/bin"
mkdir -p "$INSTALL_DIR"

# ---------- download & extract -----------------------------------------------

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

# ---------- install binaries -------------------------------------------------

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
if "$INSTALL_DIR/aeneas" --help >/dev/null 2>&1; then
    info "aeneas --help: OK"
else
    die "aeneas smoke test failed"
fi

if "$INSTALL_DIR/charon" --help >/dev/null 2>&1; then
    info "charon --help: OK"
else
    die "charon smoke test failed"
fi

info ""
info "Done! aeneas and charon are installed in $INSTALL_DIR"
info "You can now run: cargo hax into aeneas-lean"
