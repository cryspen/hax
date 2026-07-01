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

# Read `key = "value"` from a `[section]` table of a TOML pin file. Minimal
# parser: tracks the current table, strips comments and surrounding quotes. Only
# the simple values in pins.toml are supported (no arrays/multiline).
read_pin_key() {
    local pin_file="$1" section="$2" key="$3"
    [ -f "$pin_file" ] || die "Pin file not found: $pin_file"
    awk -v want="[$section]" -v key="$key" '
        /^[[:space:]]*#/ { next }                       # full-line comment
        { sub(/[[:space:]]+#.*$/, "") }                 # inline comment
        /^[[:space:]]*\[/ {                             # table header
            hdr = $0
            gsub(/^[[:space:]]+|[[:space:]]+$/, "", hdr)
            in_section = (hdr == want)
            next
        }
        in_section && $0 ~ ("^[[:space:]]*" key "[[:space:]]*=") {
            val = $0
            sub(/^[^=]*=[[:space:]]*/, "", val)         # drop "key ="
            gsub(/^[[:space:]]+|[[:space:]]+$/, "", val)
            gsub(/^"|"$/, "", val)                       # strip surrounding quotes
            print val
            exit
        }
    ' "$pin_file"
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

# Repository URLs aeneas binaries may be downloaded from. Any other `repo` value
# in [aeneas] is rejected, so binaries can only come from a trusted source.
# (charon is always sourced from AeneasVerif/charon, unaffected by this.)
AENEAS_ALLOWED_REPOS="https://github.com/AeneasVerif/aeneas https://github.com/cryspen/aeneas"

# Pins live in pins.toml: [aeneas] has tag/commit/repo, [charon] has tag/version.
PINS="$SCRIPTPATH/pins.toml"
AENEAS_TAG="$(read_pin_key "$PINS" "aeneas" "tag")"
AENEAS_COMMIT="$(read_pin_key "$PINS" "aeneas" "commit")"
AENEAS_REPO="$(read_pin_key "$PINS" "aeneas" "repo")"
[ -n "$AENEAS_TAG" ] || die "Missing 'tag' in [aeneas] of pins.toml"
[ -n "$AENEAS_REPO" ] || die "Missing 'repo' in [aeneas] of pins.toml"
case " $AENEAS_ALLOWED_REPOS " in
    *" $AENEAS_REPO "*) ;;
    *) die "Disallowed aeneas repo in pins.toml: '$AENEAS_REPO' (allowed: $AENEAS_ALLOWED_REPOS)" ;;
esac

CHARON_TAG="$(read_pin_key "$PINS" "charon" "tag")"
CHARON_EXPECTED_VERSION="$(read_pin_key "$PINS" "charon" "version")"
[ -n "$CHARON_TAG" ] || die "Missing 'tag' in [charon] of pins.toml"

# ---------- check if already installed at the right version ------------------

check_aeneas_version() {
    local bin="$1"
    # `aeneas -version` outputs "aeneas <commit-sha>"; compare the prefix.
    local actual
    actual=$("$bin" -version 2>/dev/null | awk '{print $2}') || return 1
    [ -z "$AENEAS_COMMIT" ] || [ "${actual:0:${#AENEAS_COMMIT}}" = "$AENEAS_COMMIT" ]
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
        info "aeneas found at $AENEAS_FOUND (commit matches pin)"
        info "charon found at $CHARON_FOUND (version matches pin)"
        info "Both binaries are already installed at the correct version, skipping download."
        exit 0
    fi

    if [ "$AENEAS_OK" = false ]; then
        warn "aeneas found at $AENEAS_FOUND but commit does not match pin (expected $AENEAS_COMMIT). Will overwrite with pinned version."
    fi
    if [ "$CHARON_OK" = false ]; then
        warn "charon found at $CHARON_FOUND but version does not match pin (expected $CHARON_EXPECTED_VERSION). Will overwrite with pinned version."
    fi
fi

# ---------- download & install -----------------------------------------------

info "Pinned versions:"
info "  aeneas: $AENEAS_REPO@$AENEAS_TAG ($AENEAS_COMMIT)"
info "  charon: https://github.com/AeneasVerif/charon@$CHARON_TAG"
info "  platform: $PLATFORM"

INSTALL_DIR="${CARGO_HOME:-$HOME/.cargo}/bin"
mkdir -p "$INSTALL_DIR"

AENEAS_URL="${AENEAS_REPO}/releases/download/${AENEAS_TAG}/aeneas-${PLATFORM}.tar.gz"
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
    if check_aeneas_version "$INSTALL_DIR/aeneas"; then
        info "aeneas: OK"
    else
        warn "aeneas installed but reports '$("$INSTALL_DIR/aeneas" -version 2>/dev/null | awk '{print $2}')', expected commit $AENEAS_COMMIT"
    fi
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
