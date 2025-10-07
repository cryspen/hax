#! /usr/bin/env bash

JSON_INPUT=$(cat -)
SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )

HAX_ROOT=$(jq ".hax_root")

export INCLUDE_PATHS=$(
    echo "$HAX_ROOT"/hax-lib/proof-libs/fstar/{core,hax_lib,rust_primitives}
    echo "$HAX_ROOT"/hax-lib/proofs/fstar/extraction
)
cp "$SCRIPT_DIR/FSTAR.MAKEFILE" Makefile

make >stdout 2>stderr

cat stdout >&1
cat stderr >&2
