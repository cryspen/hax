---
weight: 1
---

# Quick start

## Setup the tools

 - <input type="checkbox" class="user-checkable"/> [Install the hax toolchain](https://github.com/cryspen/hax?tab=readme-ov-file#installation).  
   <span style="margin-right:30px;"></span>🪄 Running `cargo hax --version` should print some version info.  
   <span style="margin-right:30px;"></span><span style="opacity: 0;">🪄</span> *(from hax 0.4.0 onwards, `cargo install --locked cargo-hax` is enough for this backend: it needs no hax engine)*
 - <input type="checkbox" class="user-checkable"/> [Install Lean](https://lean-lang.org/install/)
 - <input type="checkbox" class="user-checkable"/> *(Optional, for `lean` backend only)* Aeneas and charon are downloaded automatically on first use; to pre-install them, run `cargo hax tools install` inside your crate.
 - <input type="checkbox" class="user-checkable"/> Add `hax-lib` as a dependency to your crate.  
   <span style="margin-right:30px;"></span>🪄 `cargo add --git https://github.com/cryspen/hax hax-lib`  
   <span style="margin-right:30px;"></span><span style="opacity: 0;">🪄</span> *(`hax-lib` is not mandatory, but this guide assumes it is present)*

## Partial extraction

*Note: the instructions below assume you are in the folder of the
specific crate (**not workspace!**) you want to extract.*

Run the command `cargo hax into lean` to extract every item of your
crate as Lean code in the subfolder `proofs/lean`.

**What is critical? What is worth verifying?**  
Probably, your Rust crate contains mixed kinds of code: some parts are
critical (e.g. the library functions at the core of your crate) while
some others are not (e.g. the binary driver that wraps the
library). In this case, you likely want to extract only partially your
crate, so that you can focus on the important parts.

**Using the `--start-from` flag.**  
If you want to extract a function
`your_crate::some_module::my_function`, you need to tell `hax` to
extract nothing but `my_function`:

```bash
cargo hax into --charon-args="--start-from your_crate::some_module::my_function" lean
```

This command will extract `my_function`, along with all its dependencies (other functions, type definitions, etc.) from your crate.

**Unsupported Rust code.**  
hax doesn't support all Rust constructs, e.g,
`unsafe` code or interior mutability. That is another reason
for extracting only a part of your crate.

## Start Lean verification
After extracting your Rust code to Lean, the result in the `proofs/lean` folder is a complete Lean package: besides the extracted modules under `<PkgName>/Extraction/` and the `<PkgName>/Extraction.lean` module importing them, the extraction generates a `lakefile.toml` and `lean-toolchain` pinned to the versions matching it, a root module importing the extraction and the proofs, and a `<PkgName>/Verification/` folder for handwritten proofs, which hax never touches. If the crate uses external definitions, their models live in `<PkgName>/Assumptions/`: hax seeds each file there once, from the template aeneas generates, and never modifies it afterwards. You can type-check the extraction with `lake build` in `proofs/lean`, or directly in the IDE using the LSP. Contrarily to F\*, successfully building the code doesn't prove panic freedom by default.

The `Extraction/` folder and the `Extraction.lean` module next to it are owned by hax: both are rewritten on every extraction, so edits there are lost. Everything you write belongs in `Verification/` (proofs) or `Assumptions/` (models of external definitions); the other files outside `Extraction/` are created only when missing, so it is safe to re-run after editing them. The root module is yours after its creation; since the extraction is reached through the single import of `<PkgName>.Extraction`, it never needs an update when the extracted files change, and hax only warns when one of its imports is missing or stale, see [the root module check](../tools.md#the-lean-root-module-check). A commented-out import (`-- import ...`) silences those warnings for a module, and for `Verification/ProofObligations.lean` it also stops hax from recreating the stub; extraction files are regenerated and `Assumptions/` files re-seeded regardless.
