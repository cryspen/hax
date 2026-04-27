#!/usr/bin/env bash
set -e

# Extracts core-models / alloc / std (this repo) and the external core-models
# submodule (hax-lib/core-models, pinned to cryspen/rust-core-models) to F* and
# Lean, and copies the result into hax-lib/proof-libs/{fstar,lean}/.

function extract_fstar() {
    go_to "core-models"
    HAX_CORE_MODELS_EXTRACTION_MODE=on cargo hax into fstar --interfaces '+!core_models::str::* +!**::num::error +!**::panicking::internal +!core_models::borrow +!core_models::default +!core_models::error +!core_models::hash +!core_models::hint +!core_models::ops::bit +!core_models::ops::arith +!core_models::fmt +!core_models::fmt::rt +!core_models::mem +!core_models::mem::*'
    cp core-models/proofs/fstar/extraction/*.fst* "$PROOF_LIBS_FSTAR_CORE/"
    HAX_CORE_MODELS_EXTRACTION_MODE=on cargo hax -C -p alloc \; into fstar --interfaces '+!**::collections::btree::** +!**::collections::vec_deque::**'
    cp alloc/proofs/fstar/extraction/*.fst* "$PROOF_LIBS_FSTAR_CORE/"

    go_to "std"
    HAX_CORE_MODELS_EXTRACTION_MODE=on cargo hax -C -p std \; into -i '-core_models::**' fstar --interfaces '+!**'
    cp proofs/fstar/extraction/*.fst* "$PROOF_LIBS_FSTAR_CORE/"
}

function extract_lean() {
    go_to "core-models"
    LEAN_FILTERS=""
    LEAN_FILTERS+=" -core_models::result::**::unwrap" # Issue #1818
    LEAN_FILTERS+=" -core_models::result::**::expect" # Issue #1818
    LEAN_FILTERS+=" -core_models::option::**::expect" # Issue #1818
    LEAN_FILTERS+=" -core_models::option::**::unwrap" # Issue #1818
    LEAN_FILTERS+=" -core_models::num::**::saturating_add"
    LEAN_FILTERS+=" -core_models::num::**::overflowing_add"
    LEAN_FILTERS+=" -core_models::num::**::saturating_sub"
    LEAN_FILTERS+=" -core_models::num::**::overflowing_sub"
    LEAN_FILTERS+=" -core_models::num::**::saturating_mul"
    LEAN_FILTERS+=" -core_models::num::**::overflowing_mul"
    LEAN_FILTERS+=" -core_models::num::**::count_ones"
    LEAN_FILTERS+=" -core_models::num::**::rem_euclid"
    LEAN_FILTERS+=" -core_models::num::**::abs"
    LEAN_FILTERS+=" -core_models::num::**::checked_add"
    LEAN_FILTERS+=" -core_models::num::**::checked_sub"
    LEAN_FILTERS+=" -core_models::num::**::checked_mul"
    LEAN_FILTERS+=" -core_models::num::**::MIN"
    LEAN_FILTERS+=" -core_models::num::**::MAX"
    LEAN_FILTERS+=" -core_models::num::**::BITS"
    LEAN_FILTERS+=" -core_models::num::**::from_be_bytes"
    LEAN_FILTERS+=" -core_models::num::**::from_le_bytes"
    LEAN_FILTERS+=" -core_models::num::**::to_be_bytes"
    LEAN_FILTERS+=" -core_models::num::**::to_le_bytes"
    LEAN_FILTERS+=" -core_models::num::**::rotate_left"
    LEAN_FILTERS+=" -core_models::num::**::rotate_right"
    LEAN_FILTERS+=" -rust_primitives::slice::array_from_fn" # hax issue #1923
    LEAN_FILTERS+=" -rust_primitives::slice::array_map" # hax issue #1923
    LEAN_FILTERS+=" -core_models::iter::traits::iterator::**" # hax issue #1923
    LEAN_FILTERS+=" -core_models::iter::adapters::map::**" # hax issue #1923
    LEAN_FILTERS+=" -core_models::iter::adapters::flat_map::**" # hax issue #1923
    LEAN_FILTERS+=" -core_models::iter::adapters::filter::**" # hax issue #1923
    LEAN_FILTERS+=" -core_models::array::**" # hax issue #1923
    LEAN_FILTERS+=" -alloc::slice::**::sort_by" # hax issue #1923

    LEAN_FILTERS="$(echo "$LEAN_FILTERS" | xargs)"
    HAX_CORE_MODELS_EXTRACTION_MODE=on cargo hax into -i "$LEAN_FILTERS" lean
    OUT="core-models/proofs/lean/extraction/core_models.lean"

    sed -i 's/import Hax/import Hax.core_models.prologue\nimport Hax.Tactic.HaxSpec/g' "$OUT"

    cp "$OUT" "$PROOF_LIBS_LEAN_CORE_MODELS/core_models.lean"
}

function init_vars() {
    SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
    SCRIPT_NAME="$(basename "${BASH_SOURCE[0]}")"
    SCRIPT_PATH="${SCRIPT_DIR}/${SCRIPT_NAME}"

    # SCRIPT_DIR is hax-lib/. The submodule sits at hax-lib/core-models/, std at hax-lib/std/.
    CORE_MODELS_DIR="$SCRIPT_DIR/core-models"
    STD_DIR="$SCRIPT_DIR/std"
    PROOF_LIBS_FSTAR_CORE="$SCRIPT_DIR/proof-libs/fstar/core"
    PROOF_LIBS_LEAN_CORE_MODELS="$SCRIPT_DIR/proof-libs/lean/Hax/core_models"

    if [ ! -f "$CORE_MODELS_DIR/Cargo.toml" ]; then
        echo "[$SCRIPT_NAME] error: $CORE_MODELS_DIR is missing — run 'git submodule update --init hax-lib/core-models'"
        exit 1
    fi

    if [ -t 1 ]; then
        BLUE='\033[34m'
        GREEN='\033[32m'
        BOLD='\033[1m'
        RESET='\033[0m'
    else
        BLUE=''
        GREEN=''
        BOLD=''
        RESET=''
    fi
}

function go_to() {
    case "$1" in
        core-models) cd "$CORE_MODELS_DIR" ;;
        std)         cd "$STD_DIR" ;;
        *)           echo "go_to: unknown target '$1'"; exit 1 ;;
    esac
}

function msg() {
    echo -e "$1[$SCRIPT_NAME]$RESET $2"
}


function help() {
    echo "Script to extract core-models (external submodule) and std (local) to F* or Lean, and copy the result into proof-libs."
    echo ""
    echo "Usage: $0 [COMMAND]"
    echo ""
    echo "Commands:"
    echo ""
    grep '[#]>' "$SCRIPT_PATH" | sed 's/[)] #[>]/\t/g'
    echo ""
}

function cli() {
    if [ -z "$1" ]; then
        help
        exit 1
    fi

    case "$1" in
        --help) #> Show help message
            help;;
        extract) #> Extract the F* and/or Lean code and copy it to proof-libs. Use `extract fstar` for F*, `extract lean` for Lean, or `extract` for both
            case "$2" in
                "")  # no subcommand -> run both
                    extract_fstar
                    extract_lean
                    msg "$GREEN" "done"
                    ;;
                fstar)
                    extract_fstar
                    msg "$GREEN" "done"
                    ;;
                lean)
                    extract_lean
                    msg "$GREEN" "done"
                    ;;
                *)
                    echo "Invalid option for extract: $2"
                    help
                    exit 1
                    ;;
            esac
            ;;
        *)
            echo "Invalid option: $1"
            help
            exit 1;;
    esac
}

init_vars

cli "$@"
