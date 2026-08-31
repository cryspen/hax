---
weight: -5
---

# Introduction

hax is a tool for high assurance translations of a large subset of
Rust into formal languages such as [Lean](https://lean-lang.org/), [F\*](https://www.fstar-lang.org/) or [Rocq](https://rocq-prover.org/).

## Usage

hax is a cargo subcommand. 
The command `cargo hax` accepts the following subcommands:

* **`into`** (`cargo hax into BACKEND`): translate a Rust crate to the backend `BACKEND` (e.g. `lean`, `fstar`, `coq`).
* **`extract`** (`cargo hax extract [NAME...]`): run the [proof scenarios](tools.md#proof-scenarios) declared in `hax.toml`; without names, every scenario in scope runs.
* **`json`** (`cargo hax json`): extract the typed AST of your crate as a JSON file.
* **`tools`** (`cargo hax tools SUBCOMMAND`): [manage the external tools](tools.md) hax depends on (e.g. Charon and Aeneas).
 
Note:

* `BACKEND` can be `lean`, `legacy-lean`, `fstar`, `coq`, `pro-verif`, `ssprove` or `easycrypt`. See the [backend overview](https://github.com/cryspen/hax#backends) for the maturity of each backend. This manual covers the [Lean](lean/index.md) and [F\*](fstar/index.md) backends.
* The subcommands `cargo hax`, `cargo hax into` and `cargo hax into
   <BACKEND>` take options. For instance, you can `cargo hax into
   fstar --z3rlimit 100`. Use `--help` on those subcommands to list
   all options.

## Installation

hax is supported on Linux (`x86_64` and `aarch64`) and macOS (`aarch64`). Windows is not supported; use [WSL](https://learn.microsoft.com/windows/wsl/) there.

All methods below install hax itself; the target provers (Lean, F\*, ...) must be installed separately (see the quick start of the respective backend).

### For the Lean backend

The Lean backend runs the [Charon](https://github.com/AeneasVerif/charon) + [Aeneas](https://github.com/AeneasVerif/aeneas) pipeline instead of the hax engine, so from hax 0.4.0 onwards it needs no other hax component than the `cargo-hax` binary.

Prerequisites: a C compiler and [`rustup`](https://rustup.rs/) (used by Charon at extraction time).

```bash
cargo install --locked cargo-hax
```

To skip that build, use [`cargo-binstall`](https://github.com/cargo-bins/cargo-binstall) to download the binary the release published: `cargo binstall cargo-hax`.

Aeneas and Charon themselves need no install step: hax downloads pre-built binaries on demand. See [Managing tool versions](tools.md) for how they are managed, pinning versions per project, and using your own binaries.

### For all backends

The F\*, Rocq/Coq, ProVerif, SSProve, EasyCrypt, and legacy Lean backends need the hax frontend driver and engine as well. Each method below installs everything, including `cargo-hax`:

#### Manual installation

Prerequisites: a C compiler, [`opam`](https://opam.ocaml.org/), [`rustup`](https://rustup.rs/), [`nodejs`](https://nodejs.org/), and [`jq`](https://jqlang.github.io/jq/).

1. Clone this repo: `git clone https://github.com/cryspen/hax.git && cd hax`
2. Create (or use an existing) opam *switch* by running `opam switch create hax 5.4.1`
3. Run the `setup.sh` script: `./setup.sh`
4. Run `cargo hax --help`

Note: Please make sure that `$HOME/.cargo/bin` is in your `$PATH`, as
that is where `setup.sh` will install hax.

#### Nix

Prerequisites: the [Nix package manager](https://nixos.org/) with [flakes](https://wiki.nixos.org/wiki/Flakes) enabled, e.g. installed via the [Determinate Nix Installer](https://github.com/DeterminateSystems/nix-installer).

Install hax with `nix profile install github:cryspen/hax`.

Alternatively, run hax on a crate without installing it (from the crate's folder): `nix run github:cryspen/hax -- into <backend>`. To speed up builds with the [hax binary cache](https://app.cachix.org/cache/hax), run `cachix use hax`.

In any of the Nix commands above, replace `github:cryspen/hax` by `./some-dir` to compile a local checkout of hax that lives in `./some-dir`.

#### Docker

Prerequisites: [Docker](https://docs.docker.com/get-started/get-docker/).

1. Clone this repo: `git clone https://github.com/cryspen/hax.git && cd hax`
2. Build the docker image: `docker build -f .docker/Dockerfile . -t hax`
3. Get a shell: `docker run -it --rm -v /some/dir/with/a/crate:/work hax bash`

Inside the container, hax is invoked as `cargo-hax` instead of `cargo hax`.

