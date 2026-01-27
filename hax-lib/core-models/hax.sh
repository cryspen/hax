#!/usr/bin/env bash
set -e

function extract_fstar() {
    go_to "./"
    HAX_CORE_MODELS_EXTRACTION_MODE=on cargo hax into fstar --interfaces '+!core_models::str::* +!**::num::error +!**::panicking::internal +!core_models::borrow +!core_models::default +!core_models::error +!core_models::hash +!core_models::hint +!core_models::ops::bit +!core_models::ops::arith +!core_models::fmt +!core_models::fmt::rt +!core_models::mem +!core_models::mem::*'
    cp proofs/fstar/extraction/*.fst* ../proof-libs/fstar/core
    HAX_CORE_MODELS_EXTRACTION_MODE=on cargo hax -C -p std \; into -i '-core_models::**' fstar --interfaces '+!**' 
    cp std/proofs/fstar/extraction/*.fst* ../proof-libs/fstar/core
    HAX_CORE_MODELS_EXTRACTION_MODE=on cargo hax -C -p alloc \; into fstar --interfaces '+!**::collections::btree::** +!**::collections::vec_deque::**' 
    cp alloc/proofs/fstar/extraction/*.fst* ../proof-libs/fstar/core
    HAX_CORE_MODELS_EXTRACTION_MODE=on cargo hax -C -p rand_core \; into fstar --interfaces '+!**' 
    cp rand_core/proofs/fstar/extraction/*.fst* ../proof-libs/fstar/core
}

function extract_lean() {
    go_to "./"
    LEAN_FILTERS=""
    LEAN_FILTERS+=" -core_models::ops::function::Fn" # Issue #1710
    LEAN_FILTERS+=" -core_models::result::**::ok" # Issue #1823
    LEAN_FILTERS+=" -core_models::result::**::unwrap" # Issue #1818
    LEAN_FILTERS+=" -core_models::result::**::expect" # Issue #1818
    LEAN_FILTERS+=" -core_models::option::**::expect" # Issue #1818
    LEAN_FILTERS+=" -core_models::option::**::unwrap" # Issue #1818
    LEAN_FILTERS+=" -core_models::iter::traits::iterator::**" # Issue #1710
    LEAN_FILTERS+=" -core_models::array::TryFromSliceError"
    LEAN_FILTERS+=" -core_models::array::**::as_slice"
    LEAN_FILTERS+=" -core_models::array::**::map"
    LEAN_FILTERS+=" -core_models::array::**::from_fn"
    LEAN_FILTERS+=" -core_models::array::iter::IntoIter"
    LEAN_FILTERS+=" -core_models::Convert::impl_6"
    LEAN_FILTERS+=" -core_models::mem::copy"
    LEAN_FILTERS+=" -core_models::num::**::wrapping_add"
    LEAN_FILTERS+=" -core_models::num::**::saturating_add"
    LEAN_FILTERS+=" -core_models::num::**::overflowing_add"
    LEAN_FILTERS+=" -core_models::num::**::wrapping_sub"
    LEAN_FILTERS+=" -core_models::num::**::saturating_sub"
    LEAN_FILTERS+=" -core_models::num::**::overflowing_sub"
    LEAN_FILTERS+=" -core_models::num::**::wrapping_mul"
    LEAN_FILTERS+=" -core_models::num::**::saturating_mul"
    LEAN_FILTERS+=" -core_models::num::**::overflowing_mul"
    LEAN_FILTERS+=" -core_models::num::**::pow"
    LEAN_FILTERS+=" -core_models::num::**::count_ones"
    LEAN_FILTERS+=" -core_models::num::**::from_str_radix"
    LEAN_FILTERS+=" -core_models::num::**::rem_euclid"
    LEAN_FILTERS+=" -core_models::num::**::abs"
    LEAN_FILTERS+=" -core_models::num::**::checked_add"
    LEAN_FILTERS+=" -core_models::num::**::checked_sub"
    LEAN_FILTERS+=" -core_models::num::**::checked_mul"
    LEAN_FILTERS+=" -core_models::num::**::MIN"
    LEAN_FILTERS+=" -core_models::num::**::MAX"
    LEAN_FILTERS+=" -core_models::num::**::BITS"
    LEAN_FILTERS+=" -core_models::slice::iter::**"
    LEAN_FILTERS+=" -core_models::slice::**::len"
    LEAN_FILTERS+=" -core_models::slice::**::iter"
    LEAN_FILTERS+=" -core_models::slice::**::is_empty"
    LEAN_FILTERS+=" -core_models::slice::**::binary_search"
    LEAN_FILTERS+=" -core_models::slice::**::copy_from_slice"
    LEAN_FILTERS+=" -core_models::slice::**::clone_from_slice"
    LEAN_FILTERS+=" -core_models::slice::**::chunks"
    LEAN_FILTERS+=" -core_models::slice::**::chunks_exact"
    LEAN_FILTERS+=" -core_models::slice::**::split_at"
    LEAN_FILTERS+=" -core_models::slice::**::split_at_checked"
    LEAN_FILTERS+=" -core_models::ops::deref::**"
    LEAN_FILTERS+=" -core_models::iter::adapters::step_by::**"
    LEAN_FILTERS+=" -core_models::iter::adapters::take::**"
    LEAN_FILTERS+=" -core_models::iter::adapters::flat_map::**"
    LEAN_FILTERS+=" -core_models::iter::adapters::flatten::**"
    LEAN_FILTERS+=" -core_models::iter::adapters::zip::**"
    LEAN_FILTERS+=" -core_models::iter::adapters::enumerate::**"
    LEAN_FILTERS+=" -core_models::iter::adapters::map::**"
    LEAN_FILTERS+=" -core_models::ops::range::**"
    LEAN_FILTERS+=" -core_models::f32::**::abs"
    
    LEAN_FILTERS="$(echo "$LEAN_FILTERS" | xargs)"
    HAX_CORE_MODELS_EXTRACTION_MODE=on cargo hax into -i "$LEAN_FILTERS" lean
    sed -i 's/import Hax/import Hax.Core/g' proofs/lean/extraction/Core_models.lean
    sed -i 's/def Core_models\.Cmp\.Ordering /def Core_models.Cmp.Ordering_ /g' proofs/lean/extraction/Core_models.lean # Issue #1646
    sed -i 's/Core_models.Convert.From.from/Core_models.Convert.From._from/g' proofs/lean/extraction/Core_models.lean # Issue #1853
    
    cp proofs/lean/extraction/Core_models.lean ../proof-libs/lean/Hax/CoreModels.lean
}

function init_vars() {
    SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
    SCRIPT_NAME="$(basename "${BASH_SOURCE[0]}")"
    SCRIPT_PATH="${SCRIPT_DIR}/${SCRIPT_NAME}"

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
    ROOT="$SCRIPT_DIR"
    cd "$ROOT"
    cd "$1"
}

function msg() {
    echo -e "$1[$SCRIPT_NAME]$RESET $2"
}


function help() {
    echo "Script to extract to F* or Lean and place the result in proof-libs"
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
    # Check if an argument was provided

    case "$1" in
        --help) #> Show help message
            help;;
        extract) #> Extract the F* code and copy it to proof-libs. Use `extract fstar` for F*, `extract lean` for Lean, or `extract` for both
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
