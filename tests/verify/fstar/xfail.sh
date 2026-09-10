#!/usr/bin/env bash
# Asserts that the snapshots under `<test>/fstar-xfail/` are still rejected.
# `@fail(tc)` only ever meant "skip the prover", so a directive that has gone
# stale over-claims and nothing notices.
#
# Called from the Makefile, which passes the flags and the directories to check.
# Each snapshot gets its own cache and reads the verified closure from
# $CACHE_DIR through `--include`, so a failing run never writes there.
set -uo pipefail

: "${FSTAR_BIN:?}" "${FSTAR_FLAGS:?}" "${CACHE_DIR:?}" "${XFAIL_CACHE:?}" "${SNAPSHOTS:?}"

check() {
  local dir=$1 name cache
  # `check` runs in a fresh shell under `xargs`; assert here, where they are
  # used, that the Makefile really passed these through the environment.
  : "${FSTAR_BIN:?}" "${FSTAR_FLAGS:?}" "${CACHE_DIR:?}" "${XFAIL_CACHE:?}" "${SNAPSHOTS:?}"
  name=${1#"$SNAPSHOTS/"}
  cache=$XFAIL_CACHE/${name//\//_}
  rm -rf -- "$cache" && mkdir -p -- "$cache"
  # shellcheck disable=SC2086
  if $FSTAR_BIN $FSTAR_FLAGS --cache_dir "$cache" --include "$CACHE_DIR" \
       --include "$dir" "$dir"/*.fst > "$cache/log" 2>&1; then
    printf '[XFAIL] %s: type-checks, but a `@fail(tc)` directive says it must not\n' \
      "${name%/fstar-xfail}"
    return 1
  fi
  printf '[XFAIL] %s\n' "${name%/fstar-xfail}"
}
export -f check

printf '%s\n' "$@" | xargs -r -P "${JOBS:-$(nproc)}" -I{} bash -c 'check "$1"' _ {}
