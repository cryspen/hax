#!/usr/bin/env python3
"""Check that every function inside a `proptest!` block carries exactly one
`#[test]`.

`proptest!` emits `$(#[$meta])* fn $name(...)` more or less verbatim, so a
function without a `#[test]` is generated but never registered: `cargo test`
reports nothing, and the coverage gate cannot see it whenever another test
reaches the same lines. Two `#[test]`s register it twice.

Run from `hax-lib/core-models`; `make test-attributes` does.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOTS = [
    "core-models/src",
    "alloc/src",
    "std/src",
    "rand_core/src",
    "rust_primitives/src",
    "tests/client_test/src",
    "tests/rust_lean_equiv_test/source/src",
]

FN_RE = re.compile(r"\s*fn (\w+)\s*\(")
PROPTEST_RE = re.compile(r"\bproptest!\s*\{")


def check(path: Path) -> list[str]:
    """Return one message per offending function in `path`."""
    problems: list[str] = []
    lines = path.read_text().split("\n")
    depth: int | None = None  # brace depth inside a `proptest!` block, else None
    for i, line in enumerate(lines):
        if depth is None:
            if PROPTEST_RE.search(line):
                depth = line.count("{") - line.count("}")
            continue

        m = FN_RE.match(line)
        if m and depth >= 1:
            # Walk back over the attribute/comment run introducing this `fn`.
            j, n_test = i - 1, 0
            while j >= 0 and (
                lines[j].strip().startswith("#[")
                or lines[j].strip().startswith("//")
                or not lines[j].strip()
            ):
                if lines[j].strip() == "#[test]":
                    n_test += 1
                j -= 1
            if n_test == 0:
                problems.append(
                    f"{path}:{i + 1}: `{m.group(1)}` has no `#[test]`, so it never runs"
                )
            elif n_test > 1:
                problems.append(
                    f"{path}:{i + 1}: `{m.group(1)}` has {n_test} `#[test]` attributes, "
                    f"so it runs {n_test} times"
                )

        depth += line.count("{") - line.count("}")
        if depth <= 0:
            depth = None
    return problems


def main() -> int:
    problems: list[str] = []
    seen = 0
    for root in ROOTS:
        for path in sorted(Path(root).rglob("*.rs")):
            seen += 1
            problems += check(path)
    if problems:
        for p in problems:
            print(p, file=sys.stderr)
        print(
            "::error::each `fn` inside a `proptest!` block needs exactly one "
            "`#[test]`; without it the function is generated but never runs, and "
            "with two it runs twice",
            file=sys.stderr,
        )
        return 1
    print(f"test attributes: {seen} files, all `proptest!` functions run exactly once")
    return 0


if __name__ == "__main__":
    sys.exit(main())
