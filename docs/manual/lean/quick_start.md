---
weight: 1
---

# Quick start

## Setup the tools

 - <input type="checkbox" class="user-checkable"/> [Install the hax toolchain](https://github.com/cryspen/hax?tab=readme-ov-file#installation).  
   <span style="margin-right:30px;"></span>🪄 Running `cargo hax --version` should print some version info.
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

## Proof scenarios

Once an extraction configuration stabilizes, store it as a proof scenario in a `hax.toml` next to your `Cargo.toml` instead of retyping the flags:

```toml
[scenario.my-function]
backend = "lean"
include = ["your_crate::some_module::my_function"]
```

`cargo hax extract my-function` (or bare `cargo hax extract`, for all scenarios) then runs the pipeline with the flags compiled from the scenario, into `proofs/my-function/lean/`, with the Lean package named after the scenario (`MyFunction`). Each scenario gets its own directory and package, so several verification targets of one crate coexist. `include`, `exclude`, and `opaque` take charon name patterns; a default opaque set for derived trait impls (`Debug`, `Serialize`, ...) applies unless the scenario sets `default-opaques = false`. `cargo hax extract --dry-run` shows the effective invocation. See [the scenario reference](../tools.md#proof-scenarios) for all keys and the workspace rules.

For CI, `cargo hax extract` followed by `git diff --exit-code` catches extraction output that was not re-committed, and `lake build` per scenario runs the verification.

## Start Lean verification
After extracting your Rust code to Lean, the result is a complete Lean package (in `proofs/lean`, or `proofs/<scenario>/lean` for a scenario run): besides the extracted modules under `<PkgName>/Extraction/`, the extraction generates a `lakefile.toml` and `lean-toolchain` pinned to the versions matching it, a root module importing the extracted files, and a `<PkgName>/Verification/` folder for handwritten proofs, which hax never touches. If the crate uses external definitions, their models live in `<PkgName>/Assumptions/`: hax seeds each file there once, from the template aeneas generates, and never modifies it afterwards. Files outside `Extraction/` are created only when missing, so it is safe to re-run after editing them. You can type-check the extraction with `lake build` in that folder, or directly in the IDE using the LSP. Contrarily to F\*, successfully building the code doesn't prove panic freedom by default.

The `Extraction/` folder itself is owned by hax: it is cleared and regenerated on every extraction, so edits there are lost. Everything you write belongs in `Verification/` (proofs) or `Assumptions/` (models of external definitions). The root module is yours after its creation; hax checks it on every run and warns when it misses an extracted file or imports one the extraction no longer produces, and the fix is editing the import line by hand. A deleted generated file comes back on the next run, unless its import in the root module is commented out (`-- import ...`): the commented import is the opt-out that suppresses both the recreation of the file and the warnings about it.
