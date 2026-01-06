#!/usr/bin/env bash
set -e

function extract_fstar() {
    go_to "./"
    HAX_CORE_MODELS_EXTRACTION_MODE=on cargo hax into -i '-**::ops::arith::** -**::convert::**' fstar --interfaces '+!**::num::* +!**::panicking::internal +!core_models::borrow +!core_models::default +!core_models::error +!core_models::hash +!core_models::hint +!core_models::num +!core_models::ops::bit'
    cp proofs/fstar/extraction/*.fst* ../proof-libs/fstar/core
}

function extract_lean() {
    go_to "./"
    HAX_CORE_MODELS_EXTRACTION_MODE=on cargo hax into -i '-**::ops::arith::** -**::convert::** -**::function::Fn -core_models::result::** +core_models::result::Result -**::expect -**::unwrap -**::mem::copy' lean
    sed -i 's/import Hax/import Hax.RustPrimitives/g' proofs/lean/extraction/Core_models.lean
    sed -i 's/def Core_models\.Cmp\.Ordering /def Core_models.Cmp.Ordering_ /g' proofs/lean/extraction/Core_models.lean
    cp proofs/lean/extraction/*.lean* ../proof-libs/lean/Hax/Core.lean
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
