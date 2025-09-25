---
weight: 100
---

# Quick start

## Setup the tools

 - <input type="checkbox" class="user-checkable"/> [Install the hax toolchain](https://github.com/hacspec/hax?tab=readme-ov-file#installation).  
   <span style="margin-right:30px;"></span>🪄 Running `cargo hax --version` should print some version info.
 - <input type="checkbox" class="user-checkable"/> [Install Lean](https://lean-lang.org/install/)
  - <input type="checkbox" class="user-checkable"/> Add `hax-lib` as a dependency to your crate, enabled only when using hax.  
   <span style="margin-right:30px;"></span>🪄 `cargo add --target 'cfg(hax)' --git https://github.com/hacspec/hax hax-lib`  
   <span style="margin-right:30px;"></span><span style="opacity: 0;">🪄</span> *(`hax-lib` is not mandatory, but this guide assumes it is present)*

## Setup the crate you want to verify

*Note: the instructions below assume you are in the folder of the specific crate (**not workspace!**) you want to extract.*


 - <input type="checkbox" class="user-checkable"/> Create the folder `proofs/lean/extraction`folder, right next to the `Cargo.toml` of the crate you want to verify.  
   <span style="margin-right:30px;"></span>🪄 `mkdir -p proofs/lean/extraction`
 - <input type="checkbox" class="user-checkable"/> Create `proofs/lean/extraction/lakefile.toml`, and add the following content:  
```toml
name = "your_crate_name"
version = "0.1.0"
defaultTargets = ["your_crate_name"]

[[lean_lib]]
name = "your_crate_name"

[[require]]
name = "Hax"
git.url = "https://github.com/cryspen/hax"
git.subDir = "hax-lib/proof-libs/lean"
rev = "main"
``` 

## Partial extraction

*Note: the instructions below assume you are in the folder of the
specific crate you want to extract.*

Run the command `cargo hax into lean` to extract every item of your
crate as F\* modules in the subfolder `proofs/lean/extraction`.

**What is critical? What is worth verifying?**  
Probably, your Rust crate contains mixed kinds of code: some parts are
critical (e.g. the library functions at the core of your crate) while
some others are not (e.g. the binary driver that wraps the
library). In this case, you likely want to extract only partially your
crate, so that you can focus on the important part.

**Using the `-i` flag.**  
If you want to extract a function
`your_crate::some_module::my_function`, you need to tell `hax` to
extract nothing but `my_function`:

```bash
cargo hax into -i '-** +your_crate::some_module::my_function' lean
```

This command will remove all items from extraction (`-**`) and add back `my_function`, along with all its dependencies (other functions, type definitions, etc.) from your crate. If you don't want the dependencies, you can use `+!` instead of `+`. See [the the FAQ](../faq/include-flags.md) or `cargo hax into --help` for more options for partial extraction.

**Unsupported Rust code.**  
hax [doesn't support every Rust
constructs](https://github.com/hacspec/hax?tab=readme-ov-file#supported-subset-of-the-rust-language),
`unsafe` code, or complicated mutation scheme. That is another reason
for extracting only a part of your crate. When running hax, if an item
of your crate, say a function `my_crate::f`, is not handled by hax,
you can remove it from the extraction target by adding  `-my_crate::f` as an option to the `-i` flag. 

## Start Lean verification
After extracting your Rust code to Lean, the result is in the `proofs/lean/extraction` folder. The
`lakefile.toml` allows you to run Lean on this folder by running `lake build` (or directly in the IDE 
using the LSP). Contrarily to F\*, successfully building the code doesn't prove panic freedom, this
happens only if the specification states that the code is panic-free. 

### Current limitations
The Lean backend of Hax is under active development, and extraction can *fail* even on supported Rust. This can come from a missing Rust feature (i.e. supported by the Hax engine but not yet by the Lean backend). Testing the same extraction target on the *F\** backend can be an easy way to check. If all the Rust features are supported, then the extracted code can fail to build if it uses definitions from Rust `core` and `std` libraries that are missing in our Lean model (in `hax-lib/proof-libs/lean`). We're actively extending it to support idiomatic code, but feel free to report it on [zulip](https://hacspec.zulipchat.com/) or [github](https://github.com/cryspen/hax/issues)
