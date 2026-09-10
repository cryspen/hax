#!/usr/bin/env bash
# Asserts that the snapshots under `<test>/legacy-lean-xfail/` are still
# rejected. `@fail(tc)` only ever meant "skip the prover", so a directive that
# has gone stale over-claims and nothing notices.
#
# `lake env lean` gives the toolchain and `LEAN_PATH` of the package next door,
# so this needs no farm entry and cannot disturb its build.
set -uo pipefail

HERE=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
SNAPSHOTS=$(git -C "$HERE" rev-parse --show-toplevel)/tests/snapshots
# Exported, not just set: `check` runs in a fresh shell under `xargs`, and an
# empty `--root` would make `lean` fail for every snapshot, so the assertion
# would pass while checking nothing.
export HERE SNAPSHOTS

check() {
  local file=$1 name out
  : "${HERE:?}" "${SNAPSHOTS:?}"
  name=${1#"$SNAPSHOTS/"}
  name=${name%/legacy-lean-xfail/new_tests.lean}
  out=$(mktemp -d)
  if (cd "$HERE" && lake env lean --root="$SNAPSHOTS" -o "$out/o.olean" "$file") \
       > "$out/log" 2>&1; then
    printf '[XFAIL] %s: type-checks, but a `@fail(tc)` directive says it must not\n' "$name"
    rm -rf -- "$out"
    return 1
  fi
  rm -rf -- "$out"
  printf '[XFAIL] %s\n' "$name"
}
export -f check

find "$SNAPSHOTS" -path '*/legacy-lean-xfail/new_tests.lean' | sort \
  | xargs -r -P "$(nproc)" -I{} bash -c 'check "$1"' _ {}
