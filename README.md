<p align="center">
  <img src="logo.svg"/>
</p>

<p align="center">
  <a href="https://hacspec.zulipchat.com/"><img src="https://img.shields.io/badge/Zulip-50ADFF?logo=Zulip&logoColor=white" alt="Zulip"></a>
  <a href="https://hax-playground.cryspen.com"><img src="https://img.shields.io/badge/try-Playground-1f6feb" alt="Playground"></a>
  <a href="https://hax.cryspen.com"><img src="https://img.shields.io/badge/docs-Website-brightgreen" alt="Website"></a>
  <a href="https://hax.cryspen.com/blog"><img src="https://img.shields.io/badge/Blog-9b59b6" alt="Blog"></a>
  <a href="LICENSE"><img src="https://img.shields.io/badge/license-Apache--2.0-blue.svg" alt="License: Apache-2.0"></a>
</p>

# Hax

Hax is a tool for translating Rust code into formal verification languages (including [F\*](https://www.fstar-lang.org/), [Lean](https://lean-lang.org/), [Coq/Rocq](https://rocq-prover.org/), and [ProVerif](https://proverif.inria.fr/)).

Formal verification uses mathematical proof to guarantee that code behaves correctly under all possible inputs — proving the complete absence of bugs like overflows, division by zero, or invalid memory access. Traditional formal methods require rewriting programs in specialized languages disconnected from practical programming, forcing developers to master complex proof frameworks and maintain separate implementations. Hax eliminates this barrier: you write regular Rust code, annotate it with specifications, and automatically extract it to multiple proof assistants. For example, the ChaCha20 stream cipher implementation in `/examples/chacha20/` compiles to production Rust while simultaneously extracting to F\* for cryptographic proofs.

<p align="center">
    <a href="https://hax-playground.cryspen.com/#fstar+tc/latest-main/gist=5252f86237adbca7fdeb7a8fea0b1648">
    Try out hax online now!
    </a>
</p>

### Why Hax?

Formal methods traditionally require mastering a specialized verification language completely independent of any programming language you know, then rewriting your entire program in that framework. This disconnection from practical software development has kept formal verification mostly confined to research labs.

**Hax removes this pain:**
- Write code in Rust — no need to learn a separate verification language first
- Annotate your Rust code with specifications using familiar attribute syntax
- Automatically extract to multiple proof assistants without manual translation
- Maintain a single codebase that both compiles to production binaries and extracts for verification
- Leverage Rust's type system and borrow checker alongside mathematical proofs

### A Simple Example

Here's how you add specifications to Rust code. We'll write pre- and post-conditions for a simple addition function:

```rust
#[hax::requires(x < 100 && y < 100)]
#[hax::ensures(|result| result == x + y && result > x && result > y)]
pub fn verified_add(x: u32, y: u32) -> u32 {
    let result = x + y;
    hax::assert!(result > x);
    hax::assert!(result > y);
    result
}
```

The `#[requires]` attribute specifies preconditions: what must be true when the function is called. The `#[ensures]` attribute specifies postconditions: what will be true about the result. The `hax::assert!` statements help guide the verification.

Hax transparently processes this code: it compiles to a regular Rust binary (with the annotations stripped out at runtime) and simultaneously extracts to verification backends like F\* or Lean. In those backends, the proof assistant verifies that no overflow can occur and that the postconditions are guaranteed to hold.

### Key Features

**Panic-Freedom**: Hax can prove your code will never panic. For example, you can prove division is safe by requiring the divisor is non-zero, or prove array accesses are in-bounds.

**Mathematical Reasoning**: Use unbounded mathematical integers (`Int`) in specifications to reason about overflow-safe arithmetic without the limitations of machine integers.

**Refinement Types**: Define custom types with built-in invariants. A `NonZero` type automatically prevents division by zero through its type signature.

**Multiple Backends**: Extract the same Rust code to F\* (for cryptographic proofs), Lean (for functional correctness), Coq (for mathematical proofs), or ProVerif (for protocol analysis).

**Loop Verification**: Add invariants and decreases clauses to prove loops terminate and maintain correctness properties.

### Architecture Overview

Hax operates through a multi-stage pipeline:

1. **Rust Compilation**: Your code compiles normally to efficient machine code
2. **THIR Extraction**: Hax captures Rust's Typed High-level Intermediate Representation
3. **Translation**: The engine transforms THIR to the target verification language
4. **Backend Generation**: Each backend produces idiomatic code for its proof assistant
5. **Verification**: You complete proofs in F\*, Lean, Coq, or analyze protocols in ProVerif

This architecture means verification happens completely separately from your production builds — annotations have zero runtime overhead.

### Supported Backends

<table align="center">
  <tr>
    <td align="center" colspan="3">
      General purpose proof assistants
    </td>
    <td align="center" colspan="2">
      Cryptography & protocols
    </td>
  </tr>
  <tr>
    <td align="center">
      <a href="https://www.fstar-lang.org/">
        F*
        <!-- <picture>
          <source srcset=".github/assets/fstar-dark.png" media="(prefers-color-scheme: dark)">
          <source srcset=".github/assets/fstar-light.png" media="(prefers-color-scheme: light)">
          <img src=".github/assets/fstar-light.png" height="40" alt="F*">
        </picture> -->
      </a>
    </td>
    <td align="center">
      <a href="https://rocq-prover.org/">
        <picture>
          <source srcset=".github/assets/rocq-dark.svg" media="(prefers-color-scheme: dark)">
          <source srcset=".github/assets/rocq-light.svg" media="(prefers-color-scheme: light)">
          <img src=".github/assets/rocq-light.svg" height="18" alt="Rocq">
        </picture>
      </a>
    </td>
    <td align="center" style="vertical-align: center; ">
      <a href="https://lean-lang.org/">
        <picture>
          <source srcset=".github/assets/lean-dark.svg" media="(prefers-color-scheme: dark)">
          <source srcset=".github/assets/lean-light.svg" media="(prefers-color-scheme: light)">
          <img src=".github/assets/lean-light.svg" height="18" alt="Lean">
        </picture>
      </a>
    </td>
    <td align="center">
      <a href="https://github.com/SSProve/ssprove">
        <picture>
          <source srcset=".github/assets/ssprove-dark.svg" media="(prefers-color-scheme: dark)">
          <source srcset=".github/assets/ssprove-light.svg" media="(prefers-color-scheme: light)">
          <img src=".github/assets/ssprove-light.svg" height="18" alt="SSProve">
        </picture>
      </a>
    </td>
    <td align="center">
      <a href="https://proverif.inria.fr/">
        <b>ProVerif</b>
      </a>
    </td>
  </tr>
  <tr>
    <!-- 🟢🟡🟠🔴 -->
    <td align="center"><sub>🟢 stable</sub></td>
    <td align="center"><sub>🟡 partial</sub></td>
    <td align="center"><sub>🚀 active dev.</sub></td>
    <td align="center"><sub>🟡 partial</sub></td>
    <td align="center"><sub>🟠 PoC</sub></td>
  </tr>
</table>

## Learn more

Here are some resources for learning more about hax:

 - [Manual](https://hax.cryspen.com/manual/index.html) (work in progress)
    + Quick start: [F*](https://hax.cryspen.com/manual/fstar/quick_start/), [Lean](https://hax.cryspen.com/manual/lean/quick_start/)
    + Tutorial: [F*](https://hax.cryspen.com/manual/fstar/tutorial/), [Lean](https://hax.cryspen.com/manual/lean/tutorial/)
 - [Examples](./examples/): the [examples directory](./examples/) contains
   a set of examples that show what hax can do for you.
 - Other [specifications](https://github.com/hacspec/specs) of cryptographic protocols.

Questions? Join us on [Zulip](https://hacspec.zulipchat.com/) or open a [GitHub Discussion](https://github.com/cryspen/hax/discussions). For bugs, file an [Issue](https://github.com/cryspen/hax/issues).

## Usage
Hax is a cargo subcommand. 
The command `cargo hax` accepts the following subcommands:
 * **`into`** (`cargo hax into BACKEND`): translate a Rust crate to the backend `BACKEND` (e.g. `fstar`, `coq`, `lean`).
 * **`json`** (`cargo hax json`): extract the typed AST of your crate as a JSON file.
 
Note:
 * `BACKEND` can be `fstar`, `lean`, `coq`, `easycrypt` or `pro-verif`. `cargo hax into --help`
   gives the full list of supported backends.
 * The subcommands `cargo hax`, `cargo hax into` and `cargo hax into
   <BACKEND>` takes options. For instance, you can `cargo hax into
   fstar --z3rlimit 100`. Use `--help` on those subcommands to list
   all options.

## Installation
<details>
  <summary><b>Manual installation</b></summary>

1. Make sure to have the following installed on your system:

- [`opam`](https://opam.ocaml.org/) (`opam switch create 5.1.1`)
- [`rustup`](https://rustup.rs/)
- [`nodejs`](https://nodejs.org/)
- [`jq`](https://jqlang.github.io/jq/)

2. Clone this repo: `git clone git@github.com:cryspen/hax.git && cd hax`
3. Run the [setup.sh](./setup.sh) script: `./setup.sh`.
4. Run `cargo-hax --help`

</details>

<details>
  <summary><b>Nix</b></summary>

 This should work on [Linux](https://nixos.org/download.html#nix-install-linux), [MacOS](https://nixos.org/download.html#nix-install-macos) and [Windows](https://nixos.org/download.html#nix-install-windows).

<details>
  <summary><b>Prerequisites:</b> <a href="https://nixos.org/">Nix package
manager</a> <i>(with <a href="https://nixos.wiki/wiki/Flakes">flakes</a> enabled)</i></summary>

  - Either using the [Determinate Nix Installer](https://github.com/DeterminateSystems/nix-installer), with the following bash one-liner:
    ```bash
    curl --proto '=https' --tlsv1.2 -sSf -L https://install.determinate.systems/nix | sh -s -- install
    ```
  - or following [those steps](https://github.com/mschwaig/howto-install-nix-with-flake-support).

</details>

+ **Run hax on a crate directly** to get F\*/Coq/Lean/... (assuming you are in the crate's folder):
   - `nix run github:hacspec/hax -- into fstar` extracts F*.

+ **Install hax**:  `nix profile install github:hacspec/hax`, then run `cargo hax --help` anywhere
+ **Note**: in any of the Nix commands above, replace `github:hacspec/hax` by `./dir` to compile a local checkout of hax that lives in `./some-dir`
+ **Setup binary cache**: [using Cachix](https://app.cachix.org/cache/hax), just `cachix use hax`

</details>

<details>
  <summary><b>Using Docker</b></summary>

1. Clone this repo: `git clone git@github.com:hacspec/hax.git && cd hax`
3. Build the docker image: `docker build -f .docker/Dockerfile . -t hax`
4. Get a shell: `docker run -it --rm -v /some/dir/with/a/crate:/work hax bash`
5. You can now run `cargo-hax --help` (notice here we use `cargo-hax` instead of `cargo hax`)

Note: Please make sure that `$HOME/.cargo/bin` is in your `$PATH`, as that is where `setup.sh` will install hax.

</details>

## Supported Subset of the Rust Language

Hax intends to support full Rust, with the one exception, promoting a functional style: mutable references (aka `&mut T`) on return types or when aliasing (see https://github.com/hacspec/hax/issues/420) are forbidden.

Each unsupported Rust feature is documented as an issue labeled [`unsupported-rust`](https://github.com/hacspec/hax/issues?q=is%3Aissue+is%3Aopen+label%3Aunsupported-rust). When the issue is labeled [`wontfix-v1`](https://github.com/hacspec/hax/issues?q=is%3Aissue+is%3Aopen+label%3Aunsupported-rust+label%3Awontfix%2Cwontfix-v1), that means we don't plan on supporting that feature soon.

Quicklinks:
 - [🔨 Rejected rust we want to support](https://github.com/hacspec/hax/issues?q=is%3Aissue+is%3Aopen+label%3Aunsupported-rust+-label%3Awontfix%2Cwontfix-v1);
 - [💭 Rejected rust we don't plan to support in v1](https://github.com/hacspec/hax/issues?q=is%3Aissue+is%3Aopen+label%3Aunsupported-rust+label%3Awontfix%2Cwontfix-v1).

## Hacking on Hax
The documentation of the internal crate of hax and its engine can be found [here for the engine](https://hax.cryspen.com/engine/index.html) and [here for the frontend](https://hax.cryspen.com/frontend/index.html).

### Edit the sources (Nix)

Just clone & `cd` into the repo, then run `nix develop .`.
You can also just use [direnv](https://github.com/nix-community/nix-direnv), with [editor integration](https://github.com/direnv/direnv/wiki#editor-integration).

### Structure of this repository

- `rust-frontend/`: Rust library that hooks in the rust compiler and extract its internal typed abstract syntax tree [**THIR**](https://rustc-dev-guide.rust-lang.org/thir.html) as JSON.
- `engine/`: the simplification and elaboration engine that translates programs from the Rust language to various backends (see `engine/backends/`). Written in OCaml.
- `rust-engine/`: an on-going rewrite of our engine from OCaml to Rust.
...
- `cli/`: the `hax` subcommand for Cargo.

### Compiling, formatting, and more
We use the [`just` command runner](https://just.systems/). If you use
Nix, the dev shell provides it automatically, if you don't use Nix, please [install `just`](https://just.systems/man/en/packages.html) on your system.

Anywhere within the repository, you can build and install in PATH (1) the Rust parts with `just rust`, (2) the OCaml parts with `just ocaml`, or (3) both with `just build`. More commands (e.g. `just fmt` to format) are available, please run `just` or `just --list` to get all the commands.

## Publications & Other material

* [📕 Tech report](https://hal.inria.fr/hal-03176482)
* [📕 HACSpec: A gateway to high-assurance cryptography](https://github.com/hacspec/hacspec/blob/master/rwc2023-abstract.pdf)
* [📕 Original hacspec paper](https://www.franziskuskiefer.de/publications/hacspec-ssr18-paper.pdf)

### Secondary literature, using hacspec:
* [📕 Last yard](https://eprint.iacr.org/2023/185)
* [📕 A Verified Pipeline from a Specification Language to Optimized, Safe Rust](https://github.com/hacspec/hacspec.github.io/blob/master/coqpl22-final61.pdf) at [CoqPL'22](https://popl22.sigplan.org/details/CoqPL-2022-papers/5/A-Verified-Pipeline-from-a-Specification-Language-to-Optimized-Safe-Rust)
* [📕 Hax - Enabling High Assurance Cryptographic Software](https://github.com/hacspec/hacspec.github.io/blob/master/RustVerify24.pdf) at [RustVerify24](https://sites.google.com/view/rustverify2024)
* [📕 A formal security analysis of Blockchain voting](https://github.com/hacspec/hacspec.github.io/blob/master/coqpl24-paper8-2.pdf) at [CoqPL'24](https://popl24.sigplan.org/details/CoqPL-2024-papers/8/A-formal-security-analysis-of-Blockchain-voting)
* [📕 Specifying Smart Contract with Hax and ConCert](https://github.com/hacspec/hacspec.github.io/blob/master/coqpl24-paper9-13.pdf) at [CoqPL'24](https://popl24.sigplan.org/details/CoqPL-2024-papers/9/Specifying-Smart-Contract-with-Hax-and-ConCert)

## Contributing

Before starting any work please join the [Zulip chat][chat-link], start a [discussion on Github](https://github.com/hacspec/hax/discussions), or file an [issue](https://github.com/hacspec/hax/issues) to discuss your contribution.


[chat-link]: https://hacspec.zulipchat.com

## Acknowledgements

[Zulip] graciously provides the hacspec & hax community with a "Zulip Cloud Standard" tier.


[Zulip]: https://zulip.com/
