---
weight: 1
---

# Quick start

## Setup the tools

 - <input type="checkbox" class="user-checkable"/> [Install the hax toolchain](https://github.com/cryspen/hax?tab=readme-ov-file#installation).  
   <span style="margin-right:30px;"></span>🪄 Running `cargo hax --version` should print some version info.
 - <input type="checkbox" class="user-checkable"/> [Install Lean](https://lean-lang.org/install/)
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
After extracting your Rust code to Lean, the result is in the `proofs/lean` folder. The
`lakefile.toml` allows you to run Lean in this folder by running `lake build` (or directly in the IDE 
using the LSP). Contrarily to F\*, successfully building the code doesn't prove panic freedom by default.
