@_default:
  just --list

# Build Rust and OCaml parts and install binaries in PATH. To build
# only OCaml parts or only Rust parts, set target to `rust` or
# `ocaml`.
@build target='rust+ocaml':
  ./.utils/rebuild.sh {{target}}

alias b := build

# alias for `build rust`
@rust:
  just build rust

# alias for `build ocaml`
@ocaml:
  just build ocaml

# `cargo expand` a crate, but sets flags and crate attributes so that the expansion is exactly what hax receives. This is useful to debug hax macros.
[no-cd]
expand *FLAGS:
  RUSTFLAGS='-Zcrate-attr=register_tool(_hax) -Zcrate-attr=feature(register_tool) --cfg hax_compilation --cfg _hax --cfg hax --cfg hax_backend_fstar --cfg hax' \
    cargo \
    $([[ "$(cargo --version)" == *nightly* ]] || echo "+nigthly") \
    expand {{FLAGS}}

# Show debug JSON emitted by the Rust engine
@debug-json N: (_ensure_command_in_path "jless" "jless (https://jless.io/)") (_ensure_command_in_path "jq" "jq (https://jqlang.github.io/jq/)")
  cat /tmp/hax-ast-debug.json | jq -s '.[{{N}}]' | jless

# Show the generated module `concrete_ident_generated.ml`, that contains all the Rust names the engine knows about. Those names are declared in the `./engine/names` crate.
@list-names:
  hax-engine-names-extract | sed '/include .val/,$d' | just _pager

# Show the Rust to OCaml generated types available to the engine.
@list-types:
  just _ensure_command_in_path ocamlformat ocamlformat
  cd engine && dune describe pp lib/types.ml \
    | sed -e '1,/open ParseError/ d' \
    | sed '/let rec pp_/,$d' \
    | ocamlformat --impl - \
    | just _pager

# Show the OCaml module `Generated_generic_printer_base`
@show-generated-printer-ml:
  just _ensure_command_in_path ocamlformat ocamlformat
  cd engine && dune describe pp lib/generated_generic_printer_base.ml \
    | ocamlformat --impl - \
    | just _pager

# Regenerate core models
core-models-extract:
  cd hax-lib/core-models && ./hax.sh extract

# Run core models tests
core-models-test:
  cargo test --manifest-path hax-lib/core-models/Cargo.toml --workspace

# Regenerate names in the Rust engine. Writes to `rust-engine/src/names/generated.rs`.
regenerate-names:
  #!/usr/bin/env bash
  OUTPUT_FILE=rust-engine/src/ast/identifiers/global_id/generated.rs
  cargo hax -C --manifest-path engine/names/Cargo.toml \; into --output-dir $(dirname -- $OUTPUT_FILE) generate-rust-engine-names
  rustfmt "$OUTPUT_FILE"

# Format all the code
fmt:
  cargo fmt
  cd engine && dune fmt

# Run hax tests
test *FLAGS:
  cargo run --release --bin test-driver -- ./tests {{FLAGS}}

# Check the tool version manifest against the artifacts it names, downloading the *default* versions only. Reaches the network.
test-tools-manifest:
  cargo test -p cargo-hax --bin cargo-hax -- --ignored manifest_artifacts \
    --skip every_listed_artifact_verifies

# Check the tool version manifest against the artifacts it names, downloading *every* listed version. Reaches the network.
test-tools-manifest-all:
  cargo test -p cargo-hax --bin cargo-hax -- --ignored every_listed_artifact_verifies

# Print the `tools-manifest.toml` entries for one version of a managed tool, e.g. `just add-tool-version aeneas nightly-2026.07.21-52fd438`. Each artifact is downloaded from the tool's `[fallback]` URL template and hashed, so a recorded checksum is never one copied from the wrong asset.
add-tool-version tool version:
  #!/usr/bin/env bash
  set -euo pipefail
  manifest="cli/subcommands/tools-manifest.toml"
  # The output goes into the tool's section of the manifest; making the version
  # a default is a separate edit to `defaults.toml`.
  #
  # The fallback templates name the same artifacts, per platform, that an
  # unlisted version installs unverified: recording a checksum for them is
  # exactly what promotes one to a verified entry.
  templates=$(awk -v tool="{{tool}}" '
    function flush() {
      if (platform != "") { print platform "\t" url "\t" entry_points }
      platform = ""; url = ""; entry_points = ""
    }
    /^\[/ {
      flush()
      if ($0 ~ "^\\[fallback\\." tool "\\.") {
        platform = $0
        sub(/^\[fallback\.[^.]+\./, "", platform)
        sub(/\]$/, "", platform)
      }
      next
    }
    platform != "" && /^url = / { url = $0; sub(/^url = "/, "", url); sub(/"$/, "", url) }
    platform != "" && /^entry_points = / { entry_points = $0 }
    END { flush() }
  ' "$manifest")
  if [ -z "$templates" ]; then
    echo "no [fallback] templates for {{tool}} in $manifest: is it a managed tool?" >&2
    exit 1
  fi
  # Hashed from the stream, so nothing lands on disk to be stale or confused
  # with another platform's asset.
  digest() {
    if command -v sha256sum > /dev/null; then sha256sum; else shasum -a 256; fi | cut -d' ' -f1
  }
  while IFS=$'\t' read -r platform template entry_points; do
    url="${template//\{version\}/{{version}}}"
    echo "fetching $url" >&2
    sha256=$(curl -fsSL --proto '=https' --tlsv1.2 "$url" | digest)
    echo "[tools.{{tool}}.\"{{version}}\".$platform]"
    echo "url = \"$url\""
    echo "sha256 = \"$sha256\""
    if [ -n "$entry_points" ]; then echo "$entry_points"; fi
    echo
  done <<< "$templates"

# Install the managed tools from their real artifacts and run them. Reaches the network, and installs into the tool cache.
test-tools-install:
  cargo test -p cargo-hax --bin cargo-hax -- --ignored host_install

# Walk the documented tool setup flow from inside an example project, the way a user would: resolution, the `hax-lib` check, and the install of what the project resolves to. Reaches the network.
test-tools-cli:
  #!/usr/bin/env bash
  set -euo pipefail
  cargo build -q -p cargo-hax --bin cargo-hax
  # `examples/` is its own workspace, so the binary is invoked by path.
  HAX="$PWD/target/debug/cargo-hax"
  cd examples/chacha20
  "$HAX" tools show
  "$HAX" tools install
  "$HAX" tools list --installed

# Serve documentation
docs: (_ensure_command_in_path "mkdocs" "mkdocs (https://www.mkdocs.org/)")
  mkdocs serve

# Check the coherency between issues labeled `marked-unimplemented` on GitHub and issues mentionned in the engine in the `Unimplemented {issue_id: ...}` errors.
@check-issues:
  just _ensure_command_in_path jq "jq (https://jqlang.github.io/jq/)"
  just _ensure_command_in_path gh "GitHub CLI (https://cli.github.com/)"
  just _ensure_command_in_path rg "ripgrep (https://github.com/BurntSushi/ripgrep)"
  just _ensure_command_in_path sd "sd (https://github.com/chmln/sd)"
  diff -U0 \
      <(gh issue -R hacspec/hax list --label 'marked-unimplemented' --json number,closed -L 200 \
           | jq '.[] | select(.closed | not) | .number' | sort -u) \
      <(rg 'issue_id:(\d+)' -Ior '$1' | sort -u) \
      | rg '^[+-]\d' \
      | sd '[-](\d+)' '#$1\t is labeled `marked-unimplemented`, but was not found in the code' \
      | sd '[+](\d+)' '#$1\t is *not* labeled `marked-unimplemented` or is closed'

# Check that the licenses of every crate and every package are compliant with `deny.toml`
check-licenses:
  #!/usr/bin/env bash
  just _ensure_command_in_path cargo-deny "cargo-deny (https://embarkstudios.github.io/cargo-deny/)"
  just _ensure_command_in_path toml2json "toml2json (https://github.com/woodruffw/toml2json)"
  echo "> Check licenses for Rust"
  cargo deny check licenses
  cd engine
  echo "> Check licenses for OCaml"
  # initialize opam if needed
  opam env >& /dev/null || opam init --no
  # pin package `hax-engine` if needed
  opam list --required-by=hax-engine --column=name,license: -s >& /dev/null || opam pin . --yes
  # Check that every pacakge matches licenses of `deny.toml`
  if opam list --required-by=hax-engine --column=name,license: -s \
     | grep -Pvi $(toml2json ../deny.toml| jq '.licenses.allow | join("|")'); then
     echo "Some licenses were non compliant to our policy (see `deny.toml`)"
  else
    echo "licenses ok"
  fi

_ensure_command_in_path BINARY NAME:
  #!/usr/bin/env bash
  command -v {{BINARY}} &> /dev/null || {
     >&2 echo -e "\033[0;31mSorry, the binary \033[1m{{BINARY}}\033[0m\033[0;31m is required for this command.\033[0m"
     >&2 echo -e "  \033[0;31m→ please install \033[1m{{NAME}}\033[0m"
     >&2 echo ""
     exit 1
  }

_pager:
  #!/usr/bin/env bash
  if command -v bat &> /dev/null; then
      bat -l ml
  else
      less
  fi

# Serve the book
[private]
@book:
  echo "We moved out from mdbook: please run 'just docs'"
  exit 1

# Runs hax twice: once with the Rust import thir, once with the OCaml one.
# Then it compares both.
diff-thir-importers DIR:
  #!/usr/bin/env bash
  # Ensures hax is built
  just b

  # Utils
  function readJSON() { cat proofs/debugger/extraction/ast.json; }
  BASE="$PWD"
  OUT="$BASE/diff-thir-importers"
  # Remove previous results (if any)
  rm -rf "$OUT"

  cd {{DIR}}
  cargo hax json -o old-thir.json
  cargo hax --experimental-full-def json -o thir.json
  cargo hax --experimental-full-def into debugger
  readJSON > rust-import-thir-ast.json
  cargo hax                         into debugger
  readJSON > ocaml-import-thir-ast.json

  mkdir "$OUT"
  mv thir.json old-thir.json *ast.json "$OUT"
  cd "$OUT"
  diff ocaml-import-thir-ast.json rust-import-thir-ast.json > diff.json
