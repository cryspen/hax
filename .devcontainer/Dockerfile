# Batteries-included image for the hax GitHub Codespaces / devcontainer.
#
# Unlike the plain-Docker base image (`.docker/Dockerfile`, which is Nix-based),
# this is built on a normal glibc distro (Debian). That matters because several
# tools ship as prebuilt FHS binaries that hardcode `/lib64/ld-linux-x86-64.so.2`
# and won't run inside a pure-Nix image:
#   - charon / charon-driver   (downloaded by install-aeneas.sh; Lean backend)
#   - the Lean toolchain + lake (downloaded by elan)
# On Debian they run natively. Nix is installed on top purely to provide hax,
# F*, and ProVerif from the `hax` Cachix cache (no from-source build).
#
# Contents:
#   - hax (cargo-hax) + F* + ProVerif   via Nix + Cachix
#   - aeneas + charon                    via install-aeneas.sh
#   - elan + Lean v4.31.0 + warm mathlib via elan + `lake exe cache get`
FROM mcr.microsoft.com/devcontainers/base:bookworm

SHELL ["/bin/bash", "-o", "pipefail", "-c"]

# Tools needed by the Nix installer and install-aeneas.sh.
RUN apt-get update \
    && apt-get install -y --no-install-recommends \
       curl xz-utils ca-certificates git gawk file tar gzip \
    && rm -rf /var/lib/apt/lists/*

# --- Nix (single-user, flakes enabled) --------------------------------------
# Keep the build sandbox at its default (on): the tool is a pure cache hit so
# nothing is built locally, and if anything ever is, the sandbox isolates its
# $HOME. `build-users-group =` is required for a single-user (root) install.
RUN mkdir -p /etc/nix \
    && printf 'experimental-features = nix-command flakes\nbuild-users-group =\n' \
       > /etc/nix/nix.conf
RUN curl -L https://nixos.org/nix/install -o /tmp/nix-install.sh \
    && sh /tmp/nix-install.sh --no-daemon \
    && rm /tmp/nix-install.sh
# USER is unset in a bare container; cachix (and some tools) require it.
ENV USER=root
ENV PATH="/root/.nix-profile/bin:/root/.elan/bin:/root/.cargo/bin:${PATH}"

# Use the hax binary cache so hax/F*/ProVerif are downloaded, not built.
RUN nix profile install nixpkgs#cachix && cachix use hax

# --- hax + F* + ProVerif ----------------------------------------------------
# Build straight from this repo, so the image always matches the checkout it
# lives in -- no pinned or floating upstream revision.
COPY . /hax-sources
# Reconstruct a clean git tree so Nix evaluates a *git* flake that honors
# .gitignore. Without this, `COPY .` is a plain directory whose ignored/extra
# files change the source hash, so hax misses the cache and rebuilds from
# source. With it, /hax-sources matches upstream and the final hax/F*/ProVerif
# outputs substitute directly from the `hax` Cachix cache (no local build).
RUN cd /hax-sources \
    && git init -q \
    && git add -A \
    && git -c user.email=hax@localhost -c user.name=hax commit -qm devcontainer-source
RUN nix profile install /hax-sources /hax-sources#fstar
# ProVerif: hax patches it (a div-by-zero fix for one example), and that patched
# build is not in any binary cache -- building it would require a working Nix
# sandbox (unavailable under rootless Podman). Install stock ProVerif from the
# flake's *own* pinned nixpkgs instead: a clean cache hit, no rev hardcoded. The
# only difference is that single example's patch, irrelevant for a try-it image.
RUN nix profile install --impure --expr \
      '(builtins.getFlake (toString /hax-sources)).inputs.nixpkgs.legacyPackages.${builtins.currentSystem}.proverif'

# Where the hax F* proof libraries live, so extracted F* can be typechecked.
# Values mirror the flake's `hax-env` (see flake.nix).
ENV HAX_PROOF_LIBS_HOME=/hax-sources/proof-libs/fstar
ENV HAX_LIBS_HOME=/hax-sources/hax-lib/proofs/fstar/extraction

# --- aeneas + charon (Lean backend) -----------------------------------------
# Native FHS binaries; they run directly on Debian. Installed to ~/.cargo/bin.
RUN cd /hax-sources && ./install-aeneas.sh

# --- Lean toolchain + warmed mathlib cache ----------------------------------
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      | sh -s -- -y --default-toolchain none
# Warm the hax Lean proof library: fetch prebuilt mathlib oleans (NEVER compile
# mathlib from source) then build, so a user's first `lake build` on extracted
# Lean is fast. Lake manifests are committed, so no `lake update` is needed.
RUN cd /hax-sources/hax-lib/proof-libs/lean \
    && lake exe cache get \
    && lake build
# Record a default toolchain so bare `lean`/`lake` work outside a project dir
# (the version was already fetched by the warm-up above; this just sets it).
RUN elan default "$(cat /hax-sources/hax-lib/proof-libs/lean/lean-toolchain)"

# --- charon toolchain (Lean backend frontend) -------------------------------
# charon (invoked by `cargo hax into lean`) is a rustc driver that locates its
# own pinned nightly via rustup, so rustup must be present -- it is separate
# from hax's Nix toolchain. charon installs the exact nightly on first use.
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs \
      | sh -s -- -y --no-modify-path --default-toolchain none

# --- runtime PATH / cargo ---------------------------------------------------
# `cargo hax …` needs a real `cargo`; hax's wrapper only exposes `cargo-hax`.
# Install the pinned nightly toolchain (a cache hit). Placed last so it does not
# invalidate the expensive layers above.
RUN nix profile install /hax-sources#rustc
# The ENV PATH above covers non-login shells (docker run, postCreateCommand).
# Login shells (a devcontainer terminal, `bash -l`) rebuild PATH from
# /etc/profile, so add our dirs there too -- else cargo/aeneas/lake vanish
# interactively.
RUN printf '%s\n' \
      'export PATH="/root/.nix-profile/bin:/root/.elan/bin:/root/.cargo/bin:$PATH"' \
      > /etc/profile.d/10-hax.sh

WORKDIR /workspaces
