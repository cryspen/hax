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

# Hax Library - Complete Documentation and Reference Guide

## Introduction

**Hax** is a tool for translating Rust code into formal verification languages (including **F\***, **Lean4**, **Coq/Rocq**, and **ProVerif**).

Formal verification uses mathematical proof to guarantee that code behaves correctly under all possible inputs—proving the complete absence of bugs like overflows, division by zero, or invalid memory access. Traditional formal methods require rewriting programs in specialized languages disconnected from practical programming, forcing developers to master complex proof frameworks and maintain separate implementations. Hax eliminates this barrier: you write regular Rust code, annotate it with specifications, and automatically extract it to multiple proof assistants. For example, the ChaCha20 stream cipher implementation in `/examples/chacha20/` compiles to production Rust while simultaneously extracting to F\* for cryptographic proofs.

Hax comprises several components working together: `hax-lib` provides the core library with types and specification constructs; `hax-lib-macros` implements the procedural macro system for annotations like preconditions and postconditions; `cargo-hax` is the command-line tool that orchestrates extraction; `hax-engine` performs the actual translation from Rust to target languages; and backend translators generate code for each proof assistant.

<p align="center">
    <a href="https://hax-playground.cryspen.com/#fstar+tc/latest-main/gist=5252f86237adbca7fdeb7a8fea0b1648">
    <b>Try out hax online now!</b>
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
    <td align="center"><sub>🟢 stable</sub></td>
    <td align="center"><sub>🟡 partial</sub></td>
    <td align="center"><sub>🚀 active dev.</sub></td>
    <td align="center"><sub>🟡 partial</sub></td>
    <td align="center"><sub>🟠 PoC</sub></td>
  </tr>
</table>

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

### Quick Start

**1. Create a new project:**
```bash
cargo new --lib my-verified-crate && cd my-verified-crate
```

**2. Add hax as a dependency:**
```bash
cargo add hax-lib
```

**3. Install the hax toolchain:**
```bash
cargo install hax-cli
```

**4. Write your verified function in `src/lib.rs`:**
```rust
use hax_lib as hax;

#[hax::requires(x < 100)]
#[hax::ensures(|result| result > x)]
pub fn increment(x: u32) -> u32 {
    x + 1
}
```

**5. Extract to a verification backend:**
```bash
cargo hax into fstar    # For F*
cargo hax into lean     # For Lean
```

The extracted code appears in `proofs/fstar/extraction/` or `proofs/lean/extraction/` respectively, ready for formal verification.

### Key Features

**Panic-Freedom**: Hax can prove your code will never panic. For example, you can prove division is safe by requiring the divisor is non-zero, or prove array accesses are in-bounds.

**Mathematical Reasoning**: Use unbounded mathematical integers (`Int`) in specifications to reason about overflow-safe arithmetic without the limitations of machine integers.

**Refinement Types**: Define custom types with built-in invariants. A `NonZero` type automatically prevents division by zero through its type signature.

**Multiple Backends**: Extract the same Rust code to F\* (for cryptographic proofs), Lean (for functional correctness), Coq (for mathematical proofs), or ProVerif (for protocol analysis).

**Loop Verification**: Add invariants and decreases clauses to prove loops terminate and maintain correctness properties.

See sections below for detailed examples of each feature.

### Learn More

Here are some resources for learning more about hax:

- **[Manual](https://hax.cryspen.com/manual/index.html)** (work in progress)
  + Quick start: [F*](https://hax.cryspen.com/manual/fstar/quick_start/), [Lean](https://hax.cryspen.com/manual/lean/quick_start/)
  + Tutorial: [F*](https://hax.cryspen.com/manual/fstar/tutorial/), [Lean](https://hax.cryspen.com/manual/lean/tutorial/)
- **[Examples](./examples/)**: the [examples directory](./examples/) contains a set of examples that show what hax can do for you.
- **Other [specifications](https://github.com/hacspec/specs)** of cryptographic protocols.

**Questions?** Join us on [Zulip](https://hacspec.zulipchat.com/) or open a [GitHub Discussion](https://github.com/cryspen/hax/discussions). For bugs, file an [Issue](https://github.com/cryspen/hax/issues).

### Architecture Overview

Hax operates through a multi-stage pipeline:

1. **Rust Compilation**: Your code compiles normally to efficient machine code
2. **THIR Extraction**: Hax captures Rust's Typed High-level Intermediate Representation
3. **Translation**: The engine transforms THIR to the target verification language
4. **Backend Generation**: Each backend produces code for its proof assistant
5. **Verification**: You complete proofs in F\*, Lean, Coq, or analyze protocols in ProVerif

This architecture means verification happens completely separately from your production builds—annotations have zero runtime overhead.

### Documentation Structure

This README provides a complete overview of all hax capabilities. For deeper dives into specific topics:

- **[hax-lib-api.md](hax-lib-api.md)**: Exhaustive API reference for every function, macro, and type
- **[macro-system-complete.md](macro-system-complete.md)**: Complete documentation of all macros and their implementations
- **[examples-patterns.md](examples-patterns.md)**: Comprehensive examples and design patterns from basic to advanced
- **[verification-techniques.md](verification-techniques.md)**: In-depth guide to proof strategies and verification patterns
- **[cli-backends.md](cli-backends.md)**: Complete CLI reference and backend-specific documentation
- **[internal-architecture.md](internal-architecture.md)**: Deep dive into hax's internal implementation
- **[errors-troubleshooting.md](errors-troubleshooting.md)**: Complete error code reference and troubleshooting guide
- **[INDEX.md](INDEX.md)**: Documentation index and navigation guide

---

## Table of Contents

### Part 1: Foundations
1. [Overview and Architecture](#1-overview-and-architecture)
   - Key Features
   - Architecture and Data Flow
   - Verification Workflow
   - Design Philosophy

2. [Core Components](#2-core-components)
   - Component Overview
   - `hax-lib` (Core Library)
   - `hax-lib-macros` (Procedural Macros)
   - `cargo-hax` (CLI Tool)
   - `hax-engine` (Translation Engine)
   - Backend Translators

3. [Getting Started](#3-getting-started)
   - Installation Methods
   - Project Setup
   - First Verified Program
   - Development Workflow

### Part 2: Core Library (hax-lib)

4. [Type System and Mathematical Abstractions](#4-type-system-and-mathematical-abstractions)
   - Mathematical Integers (`Int`)
   - Logical Propositions (`Prop`)
   - Abstraction and Concretization
   - Type Conversions and Lifting

5. [Assertions and Assumptions](#5-assertions-and-assumptions)
   - `assert!` - Provable Assertions
   - `assume!` - Trusted Assumptions
   - `assert_prop!` - Logical Propositions
   - `debug_assert!` - Runtime-Only Checks
   - Best Practices and Safety

6. [Logical Specifications](#6-logical-specifications)
   - Universal Quantification (`forall!`)
   - Existential Quantification (`exists!`)
   - Logical Implication (`implies!`)
   - Proposition Combinators
   - Writing Complex Specifications

7. [Refinement Types](#7-refinement-types)
   - Refinement Type Theory
   - The `Refinement` Trait
   - Creating Custom Refinements
   - Refinement Type Patterns
   - Advanced Usage

### Part 3: Specification and Verification

8. [Function Contracts](#8-function-contracts)
   - Preconditions (`#[requires]`)
   - Postconditions (`#[ensures]`)
   - Multiple Contracts
   - Contract Composition
   - Advanced Contract Patterns

9. [Loop Specifications](#9-loop-specifications)
   - Loop Invariants (`#[loop_invariant]`)
   - Termination Measures (`#[decreases]`)
   - Ghost Variables
   - Invariant Design Patterns
   - Complex Loop Examples

10. [Advanced Attributes](#10-advanced-attributes)
    - Opacity and Modularity `(#[opaque]`)
    - Lemmas and Auxiliary Proofs (`#[lemma]`)
    - Visibility Control (`#[exclude]`, `#[include]`)
    - Type-Level Specifications
    - Backend-Specific Attributes

### Part 4: Toolchain and Backends

11. [CLI and Toolchain](#11-cli-and-toolchain)
    - `cargo-hax` Overview
    - Complete Command Reference
    - Configuration Options
    - Environment Variables
    - Project Organization

12. [Backend Support](#12-backend-support)
    - F\* (Stable)
    - Lean4 (Active Development)
    - Coq/Rocq (Experimental)
    - ProVerif (Protocol Verification)
    - SSProve and EasyCrypt (Cryptographic Proofs)
    - Backend Comparison Matrix

### Part 5: Advanced Topics

13. [Examples and Patterns](#13-examples-and-patterns)
    - Basic Verification Patterns
    - Cryptographic Algorithms
    - Mathematical Operations
    - Data Structures
    - Protocol Verification

14. [Advanced Features](#14-advanced-features)
    - Backend-Specific Code Injection
    - Proof Optimization
    - Modularity and Scaling
    - Performance Considerations
    - Integration with External Tools

15. [Complete API Reference](#15-complete-api-reference)
    - Core Types and Traits
    - All Macros (Declarative and Procedural)
    - Functions and Methods
    - Constants and Type Aliases

16. [Resources and Community](#16-resources-and-community)
    - External Links
    - Contributing Guidelines
    - Roadmap
    - License Information

---

## Part 1: Foundations

## 1. Overview and Architecture

### Design Philosophy

Hax is built on the principle that formal verification should integrate seamlessly with existing development workflows rather than replacing them. The system allows you to write Rust code — code that follows standard Rust patterns and conventions — while adding verification capabilities through lightweight annotations. This means you don't sacrifice code quality, performance, or Rust idioms for the sake of verification.

The architecture separates concerns: your Rust code compiles normally through `rustc` for production use, while `cargo-hax` orchestrates a parallel extraction process for verification. This separation means verification has zero runtime overhead—all annotations are compile-time only.

### Architecture and Data Flow

Hax operates through a multi-stage pipeline:

1. **Rust Compilation**: Your code passes through the normal Rust compiler, benefiting from type checking, borrow checking, and macro expansion.

2. **THIR Extraction**: Hax captures Rust's Typed High-level Intermediate Representation, preserving all type information and semantic meaning.

3. **Engine Transformation**: The `hax-engine` normalizes the code, resolves traits, and performs backend-agnostic simplifications.

4. **Backend Translation**: Specialized translators generate code for each target language (F\*, Lean, Coq, ProVerif).

5. **Verification**: You work with the extracted code in your chosen proof assistant, completing proofs and analyzing correctness.

This pipeline preserves Rust's semantics while mapping constructs to appropriate equivalents in each backend.

### Verification Workflow

A typical development cycle with hax:

1. **Write and Test**: Develop your Rust code normally, using standard testing and debugging tools.

2. **Add Specifications**: Annotate functions with preconditions, postconditions, and invariants using hax attributes.

3. **Extract**: Run `cargo hax into <backend>` to generate verification code.

4. **Verify**: Work in your proof assistant to complete any remaining proofs.

5. **Iterate**: Refine specifications and strengthen invariants based on verification feedback.

The key insight: you maintain a single Rust codebase that serves both as production code and as input to formal verification, eliminating the traditional duplication problem.

---

## 2. Core Components

The hax project comprises several tightly integrated components, each with a specific role in the verification pipeline.

### 2.1 Component Overview

**hax-lib**: The core runtime library providing mathematical types (`Int`, `Prop`), abstraction traits, and declarative macros. This is what you import in your Rust code.

**hax-lib-macros**: Procedural macros for attributes like `#[requires]`, `#[ensures]`, and `#[loop_invariant]`. These expand to attach metadata that guides extraction.

**cargo-hax**: The command-line tool (`cargo hax`) that orchestrates the entire extraction process. It invokes the Rust compiler, runs the frontend, and calls the engine.

**hax-engine**: The translation engine (currently in OCaml, being rewritten in Rust) that transforms Rust's intermediate representation into backend-specific code.

**Backend Translators**: Specialized modules for each target language (F\*, Lean, Coq, ProVerif) that generate code for that proof assistant.

### 2.2 hax-lib: The Core Library

hax-lib provides the types and macros you use in your Rust code:

- **Mathematical types**: `Int` for unbounded integers, `Prop` for logical propositions
- **Specification macros**: `assert!`, `assume!`, `forall!`, `exists!`, `implies!`
- **Abstraction traits**: `Abstraction`, `Concretization`, `Refinement` for type conversions
- **Backend helpers**: Functions for injecting backend-specific code when needed

During normal compilation (`cargo build`), these constructs have minimal or zero runtime overhead—assertions become debug assertions or are stripped entirely. During extraction (`cargo hax`), they provide semantic information to the verification backends.

### 2.3 hax-lib-macros: Procedural Macros

The procedural macro crate implements attribute macros:

- `#[requires(...)]`: Preconditions
- `#[ensures(...)]`: Postconditions
- `#[loop_invariant(...)]`: Loop invariants
- `#[decreases(...)]`: Termination measures
- `#[opaque]`: Modularity control
- `#[lemma]`: Lemma designation
- `#[refinement_type]`: Refinement type definitions

These macros expand to attach metadata that hax's frontend collects during extraction.

### 2.4 cargo-hax: The CLI Tool

The `cargo hax` command provides a familiar cargo-style interface:

```bash
cargo hax into fstar     # Extract to F*
cargo hax into lean      # Extract to Lean
cargo hax into coq       # Extract to Coq
```

The CLI handles:
- Invoking rustc with hax's frontend plugin
- Collecting extracted AST
- Running the engine with appropriate options
- Managing output directories

### 2.5 hax-engine: Translation Engine

The engine performs the core transformation from Rust's intermediate representation to backend languages. It:

- Normalizes Rust's THIR to a simpler AST
- Resolves traits and desugars patterns
- Applies backend-agnostic simplifications
- Routes to appropriate backend translator

### 2.6 Backend Translators

Each backend translator understands both Rust semantics and the target language:

- **F\* backend**: Generates F\* code with SMT-friendly encoding
- **Lean backend**: Produces Lean code emphasizing panic-freedom
- **Coq backend**: Creates Coq definitions for mathematical proofs
- **ProVerif backend**: Extracts protocol models for security analysis

### 2.7 Repository Structure

For contributors and those interested in hax's internals:

```
hax/
├── rust-frontend/        # Rust compiler hook that extracts THIR as JSON
├── engine/              # Translation engine (OCaml)
│   └── backends/        # Backend translators (F*, Lean, Coq, etc.)
├── rust-engine/         # Ongoing Rust rewrite of the engine
...
└── cli/                 # The `hax` cargo subcommand
```

- **rust-frontend/**: Rust library that hooks into the Rust compiler and extracts its internal typed abstract syntax tree [**THIR**](https://rustc-dev-guide.rust-lang.org/thir.html) as JSON.
- **engine/**: The simplification and elaboration engine that translates programs from Rust to various backends. Written in OCaml.
- **rust-engine/**: An ongoing rewrite of the engine from OCaml to Rust.
- **cli/**: The `hax` subcommand for Cargo.

---

## 3. Getting Started

### 3.1 Installation Methods

#### Method 1: Nix (Recommended)

This should work on [Linux](https://nixos.org/download.html#nix-install-linux), [MacOS](https://nixos.org/download.html#nix-install-macos), and [Windows](https://nixos.org/download.html#nix-install-windows).

**Prerequisites:** [Nix package manager](https://nixos.org/) with [flakes](https://nixos.wiki/wiki/Flakes) enabled

- Either using the [Determinate Nix Installer](https://github.com/DeterminateSystems/nix-installer):
  ```bash
  curl --proto '=https' --tlsv1.2 -sSf -L https://install.determinate.systems/nix | sh -s -- install
  ```
- Or following [these steps](https://github.com/mschwaig/howto-install-nix-with-flake-support).

**Usage:**

```bash
# Run hax directly on a crate (assuming you're in the crate's folder)
nix run github:hacspec/hax -- into fstar

# Install hax globally
nix profile install github:hacspec/hax

# Verify installation
cargo hax --help
```

**Note:** Replace `github:hacspec/hax` with `./dir` to compile a local checkout of hax.

**Setup binary cache:** Using [Cachix](https://app.cachix.org/cache/hax), just run:
```bash
cachix use hax
```

#### Method 2: Manual Installation

**Prerequisites:**
1. [`opam`](https://opam.ocaml.org/) (`opam switch create 5.1.1`)
2. [`rustup`](https://rustup.rs/)
3. [`nodejs`](https://nodejs.org/)
4. [`jq`](https://jqlang.github.io/jq/)

**Installation steps:**

```bash
# 1. Clone the repository
git clone git@github.com:cryspen/hax.git && cd hax

# 2. Run the setup script
./setup.sh

# 3. Verify installation
cargo-hax --help
```

**Note:** Please make sure that `$HOME/.cargo/bin` is in your `$PATH`.

#### Method 3: Docker (Isolated Environment)

For containerized environments:

```bash
# 1. Clone the repository
git clone git@github.com:hacspec/hax.git && cd hax

# 2. Build the Docker image
docker build -f .docker/Dockerfile . -t hax

# 3. Get a shell
docker run -it --rm -v /path/to/your/crate:/work hax bash

# 4. Inside container, you can now run:
cd /work
cargo-hax --help
```

**Note:** In Docker, use `cargo-hax` instead of `cargo hax`.

### 3.2 Using Hax

Hax is a cargo subcommand. The command `cargo hax` accepts the following subcommands:

- **`into`** (`cargo hax into BACKEND`): Translate a Rust crate to the backend `BACKEND` (e.g., `fstar`, `coq`, `lean`).
- **`json`** (`cargo hax json`): Extract the typed AST of your crate as a JSON file.

**Notes:**
- `BACKEND` can be `fstar`, `lean`, `coq`, `easycrypt`, or `pro-verif`. Run `cargo hax into --help` for the full list of supported backends.
- The subcommands `cargo hax`, `cargo hax into`, and `cargo hax into <BACKEND>` accept options. For instance, you can run `cargo hax into fstar --z3rlimit 100`. Use `--help` on those subcommands to list all options.

### 3.3 Creating Your First Verified Program

```bash
# Create new library
cargo new --lib my-verified-lib
cd my-verified-lib

# Add hax-lib
cargo add hax-lib
```

Write some verified code in `src/lib.rs`:

```rust
use hax_lib as hax;

#[hax::requires(x < 100)]
#[hax::ensures(|result| result > x)]
pub fn increment(x: u32) -> u32 {
    x + 1
}
```

Test and extract:

```bash
# Test normally
cargo test

# Extract to F*
cargo hax into fstar

# View generated code
ls proofs/fstar/extraction/
```

---

## Supported Subset of the Rust Language

Hax intends to support full Rust, with one exception: we promote a functional style where mutable references (`&mut T`) on return types or when aliasing are forbidden (see [issue #420](https://github.com/hacspec/hax/issues/420)).

Each unsupported Rust feature is documented as an issue labeled [`unsupported-rust`](https://github.com/hacspec/hax/issues?q=is%3Aissue+is%3Aopen+label%3Aunsupported-rust). When the issue is also labeled [`wontfix-v1`](https://github.com/hacspec/hax/issues?q=is%3Aissue+is%3Aopen+label%3Aunsupported-rust+label%3Awontfix%2Cwontfix-v1), that means we don't plan on supporting that feature soon.

**Quick links:**
- [🔨 Rejected Rust we want to support](https://github.com/hacspec/hax/issues?q=is%3Aissue+is%3Aopen+label%3Aunsupported-rust+-label%3Awontfix%2Cwontfix-v1)
- [💭 Rejected Rust we don't plan to support in v1](https://github.com/hacspec/hax/issues?q=is%3Aissue+is%3Aopen+label%3Aunsupported-rust+label%3Awontfix%2Cwontfix-v1)

The rest of this document provides comprehensive details on all hax features. The sections continue below with the complete type system, macro reference, backend documentation, and advanced examples.

---

## Part 2: Core Library (hax-lib)


## Hacking on Hax

The documentation of the internal crates of hax and its engine can be found:
- [Engine documentation](https://hax.cryspen.com/engine/index.html)
- [Frontend documentation](https://hax.cryspen.com/frontend/index.html)

### Edit the Sources (Nix)

Just clone & `cd` into the repo, then run `nix develop .`.

You can also use [direnv](https://github.com/nix-community/nix-direnv), with [editor integration](https://github.com/direnv/direnv/wiki#editor-integration).

### Compiling, Formatting, and More

We use the [`just` command runner](https://just.systems/). If you use Nix, the dev shell provides it automatically. If you don't use Nix, please [install `just`](https://just.systems/man/en/packages.html) on your system.

Anywhere within the repository, you can:
- Build and install Rust parts: `just rust`
- Build OCaml parts: `just ocaml`
- Build both: `just build`
- Format code: `just fmt`

Run `just` or `just --list` to see all available commands.

---

## Publications & Other Material

### Core Publications

* [📕 Tech report](https://hal.inria.fr/hal-03176482)
* [📕 HACSpec: A gateway to high-assurance cryptography](https://github.com/hacspec/hacspec/blob/master/rwc2023-abstract.pdf)
* [📕 Original hacspec paper](https://www.franziskuskiefer.de/publications/hacspec-ssr18-paper.pdf)

### Secondary Literature Using hacspec/hax

* [📕 Last yard](https://eprint.iacr.org/2023/185)
* [📕 A Verified Pipeline from a Specification Language to Optimized, Safe Rust](https://github.com/hacspec/hacspec.github.io/blob/master/coqpl22-final61.pdf) at [CoqPL'22](https://popl22.sigplan.org/details/CoqPL-2022-papers/5/A-Verified-Pipeline-from-a-Specification-Language-to-Optimized-Safe-Rust)
* [📕 Hax - Enabling High Assurance Cryptographic Software](https://github.com/hacspec/hacspec.github.io/blob/master/RustVerify24.pdf) at [RustVerify24](https://sites.google.com/view/rustverify2024)
* [📕 A formal security analysis of Blockchain voting](https://github.com/hacspec/hacspec.github.io/blob/master/coqpl24-paper8-2.pdf) at [CoqPL'24](https://popl24.sigplan.org/details/CoqPL-2024-papers/8/A-formal-security-analysis-of-Blockchain-voting)
* [📕 Specifying Smart Contract with Hax and ConCert](https://github.com/hacspec/hacspec.github.io/blob/master/coqpl24-paper9-13.pdf) at [CoqPL'24](https://popl24.sigplan.org/details/CoqPL-2024-papers/9/Specifying-Smart-Contract-with-Hax-and-ConCert)

---

## 16. Resources and Community

### 16.1 External Links

- **GitHub**: https://github.com/hacspec/hax
- **Website**: https://hax.cryspen.com
- **Playground**: https://hax-playground.cryspen.com
- **Documentation**: https://hax.cryspen.com/manual/
- **Zulip Chat**: https://hacspec.zulipchat.com/
- **Blog**: https://hax.cryspen.com/blog

### 16.2 Related Documentation

The comprehensive technical documentation continues in these specialized files:

- **[hax-lib-api.md](hax-lib-api.md)**: Complete API reference for types, traits, and functions
- **[macro-system-complete.md](macro-system-complete.md)**: Exhaustive documentation of all macros
- **[examples-patterns.md](examples-patterns.md)**: Comprehensive examples from basic to cryptographic algorithms
- **[verification-techniques.md](verification-techniques.md)**: Proof strategies and verification workflows
- **[cli-backends.md](cli-backends.md)**: Complete CLI reference and all backend documentation
- **[errors-troubleshooting.md](errors-troubleshooting.md)**: Error codes and debugging strategies
- **[internal-architecture.md](internal-architecture.md)**: Deep dive into hax's implementation

### 16.3 Contributing

Before starting any work, please join the [Zulip chat](https://hacspec.zulipchat.com/), start a [discussion on Github](https://github.com/hacspec/hax/discussions), or file an [issue](https://github.com/hacspec/hax/issues) to discuss your contribution.

We welcome contributions of all kinds—bug reports, documentation improvements, new features, and more!

### 16.4 License

The hax library is licensed under Apache-2.0. See the [LICENSE](LICENSE) file for details.

### 16.5 Acknowledgements

[Zulip](https://zulip.com/) graciously provides the hacspec & hax community with a "Zulip Cloud Standard" tier.
