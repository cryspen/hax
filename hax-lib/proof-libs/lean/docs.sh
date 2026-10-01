#!/usr/bin/env bash
# Generate the Lean docs for CoreModels and Hax

set -eu

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

cd "$DIR/docbuild"

rm -rf .lake
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake build CoreModels:docs Hax:docs
printf "To open the docs, run:\n    \033[1m(cd $DIR/docbuild/.lake/build/doc && python3 -m http.server)\033[0m\n"
