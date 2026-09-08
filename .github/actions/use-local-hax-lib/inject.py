#!/usr/bin/env python3
"""Point a project's `hax-lib` dependencies at a local hax checkout, and
verify that they actually resolved there.

`cargo-hax` accepts exactly the `hax-lib` of its own version
(`cli/cargo-hax/src/tools/haxlib.rs`), so testing a hax branch against a
project means making the project build against *that* branch's `hax-lib`.

The obvious way to do that, a `[patch.crates-io]` entry, does not work: a
patch is only applied when its version satisfies the requirement the project
declares, and a hax under development rarely does (`0.4.0-rc.1` against a
project asking for `^0.3.7`). Cargo then keeps the published crate and says
so in a note nobody reads, and the run fails much later, in `cargo hax`,
looking like a hax bug.

So the requirement itself is rewritten: every dependency on a crate that the
hax checkout provides becomes a path dependency on it, version requirement
dropped. Members that inherit the dependency (`hax-lib.workspace = true`)
need no change, since the `[workspace.dependencies]` entry they inherit from
is itself rewritten.

Which crates those are is read from the hax checkout, not hardcoded, so a
hax that gains or moves a library crate needs no change here.

A dependency spelled in a form this script does not handle is a hard error:
silently leaving it on the published crate is the failure mode above.
"""

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

# Directories that hold build output or vendored copies rather than the
# project's own manifests.
SKIP_DIRS = {".git", "target", "node_modules", "vendor", ".cargo"}


def fail(message):
    print(f"::error::{message}", file=sys.stderr)
    sys.exit(1)


def cargo_metadata(manifest, *extra):
    """Metadata for `manifest`, or a fatal error naming what cargo said."""
    command = [
        "cargo",
        "metadata",
        "--format-version",
        "1",
        "--manifest-path",
        str(manifest),
        *extra,
    ]
    result = subprocess.run(command, capture_output=True, text=True)
    if result.returncode != 0:
        fail(
            f"`{' '.join(command)}` failed:\n{result.stderr.strip()}"
        )
    return json.loads(result.stdout)


def local_crates(hax_root):
    """The crates the hax checkout provides, as name -> absolute directory.

    Workspace members only: those are the crates a project can depend on by
    path and get this checkout's code. `hax-lib/core-models` is deliberately
    outside the hax workspace and so is not among them — projects vendor
    their own copy of it.

    Restricted to the `hax-` namespace, which is every library crate a
    project annotates against. The workspace also holds crates with names a
    project could plausibly use for something of its own (`test-driver`);
    redirecting one of those to hax would be a confusing way to break a
    build that has nothing to do with hax.
    """
    metadata = cargo_metadata(hax_root / "Cargo.toml", "--no-deps")
    return {
        package["name"]: Path(package["manifest_path"]).parent
        for package in metadata["packages"]
        if package["name"].startswith("hax-")
    }


def rewrite_manifest(path, crates):
    """Rewrite `path` in place. Returns the list of redirected crate names.

    Line-based on purpose: the point is to change one key per dependency and
    leave every project manifest otherwise byte-identical, so that a build
    failure afterwards is about hax and not about this script's idea of TOML.
    """
    lines = path.read_text().splitlines(keepends=True)
    redirected = []
    section = ""

    for index, line in enumerate(lines):
        stripped = line.strip()

        header = re.fullmatch(r"\[+([^\]]+)\]+", stripped)
        if header:
            section = header.group(1)
            continue

        # `[dependencies.hax-lib]` and friends: the crate is named by the
        # section, and the keys to fix are the lines under it.
        section_crate = section.rsplit(".", 1)[-1].strip('"\'')
        if section_crate in crates and section.startswith(
            ("dependencies", "dev-dependencies", "build-dependencies",
             "workspace.dependencies", "target.")
        ):
            if re.match(r"version\s*=", stripped):
                lines[index] = re.sub(
                    r"version\s*=\s*[\"'][^\"']*[\"']",
                    f'path = "{crates[section_crate]}"',
                    line,
                )
                redirected.append(section_crate)
            elif re.match(r"path\s*=", stripped):
                # Already local, from a previous run or from the project.
                redirected.append(section_crate)
            continue

        match = re.match(r"^(\s*)([A-Za-z0-9_-]+)((?:\.[A-Za-z0-9_-]+)?)\s*=\s*(.*?)\s*$", line)
        if not match:
            continue
        indent, key, dotted, value = match.groups()

        # A renamed dependency names its crate in a `package` key.
        renamed = re.search(r"package\s*=\s*[\"']([^\"']+)[\"']", value)
        name = renamed.group(1) if renamed else key
        if name not in crates:
            continue
        local = crates[name]

        # `hax-lib.workspace = true`, or a `workspace = true` inline table:
        # the entry this inherits from is rewritten instead.
        if dotted == ".workspace" or re.search(r"\bworkspace\s*=\s*true", value):
            continue

        # `hax-lib.path = "..."`, or an inline table already carrying a
        # path: already local, nothing to redirect.
        if dotted == ".path" or re.search(r"\bpath\s*=", value):
            redirected.append(name)
            continue

        if dotted == ".version":
            lines[index] = f'{indent}{key}.path = "{local}"\n'
        elif value.startswith(("\"", "'")):
            lines[index] = f'{indent}{key} = {{ path = "{local}" }}\n'
        elif value.startswith("{") and value.endswith("}"):
            inner = value[1:-1].strip()
            if re.search(r"version\s*=", inner):
                inner = re.sub(
                    r"version\s*=\s*[\"'][^\"']*[\"']", f'path = "{local}"', inner
                )
            else:
                inner = f'path = "{local}"' + (f", {inner}" if inner else "")
            lines[index] = f"{indent}{key} = {{ {inner} }}\n"
        else:
            # A multi-line inline table, or something else unforeseen.
            # Guessing here is what this script exists to prevent.
            fail(
                f"{path}:{index + 1}: cannot redirect `{name}` to the local "
                f"checkout: unsupported dependency form `{value}`. Teach "
                f"{Path(__file__).name} this form."
            )

        if not dotted or dotted in (".version", ".path"):
            redirected.append(name)

    if redirected:
        path.write_text("".join(lines))
    return redirected


def verify(project_root, crates):
    """Check the resolve graph really points at the local checkout.

    The rewrite above can be complete and still not take effect — a stale
    lockfile entry, a vendoring config, a `[patch]` of its own. Only the
    resolved graph settles it, and it has to be settled here: the next thing
    to notice would be `cargo hax` rejecting the version, from inside the
    project's own driver script.

    What is checked is each workspace member's *direct* dependency edges,
    which is what `cargo-hax` gates on
    (`ProjectContext::load_for` in `cli/cargo-hax/src/tools/project.rs`).
    Published copies elsewhere in the graph are left alone: a project
    depending on published crates that themselves use `hax-lib` pulls in
    their `hax-lib` too, cargo keeps the two semver-incompatible versions
    side by side, and neither hax nor this check has anything to say about
    the copy the project does not compile its own annotations against.
    """
    metadata = cargo_metadata(project_root / "Cargo.toml")
    packages = {package["id"]: package for package in metadata["packages"]}
    members = set(metadata["workspace_members"])
    nodes = {node["id"]: node for node in metadata["resolve"]["nodes"]}

    published = []
    local = []
    for member in sorted(members):
        for dep in nodes[member]["deps"]:
            package = packages[dep["pkg"]]
            if package["name"] not in crates:
                continue
            edge = (packages[member]["name"], package)
            (published if package["source"] is not None else local).append(edge)

    if published:
        listing = "\n".join(
            f"  - {name} depends on {p['name']} {p['version']} from {p['source']}"
            for name, p in published
        )
        fail(
            "these direct dependencies still resolve to a published version "
            f"instead of the local hax checkout:\n{listing}\n"
            "The dependency was rewritten but the resolve graph disagrees; "
            "check for a `[patch]` section or a vendoring config in the "
            "project."
        )

    if not local:
        fail(
            "no workspace member directly depends on a hax library crate, "
            "so nothing was injected. Expected at least one of: "
            f"{', '.join(sorted(crates))}."
        )

    for name, package in local:
        print(f"{name} -> {package['name']} {package['version']} (local)")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", required=True, type=Path)
    parser.add_argument("--hax", required=True, type=Path)
    args = parser.parse_args()

    project_root = args.project.resolve()
    crates = local_crates(args.hax.resolve())

    redirected = []
    for manifest in sorted(project_root.rglob("Cargo.toml")):
        if SKIP_DIRS & set(manifest.relative_to(project_root).parts):
            continue
        for name in rewrite_manifest(manifest, crates):
            print(f"{manifest.relative_to(project_root)}: {name}")
            redirected.append(name)

    if not redirected:
        fail(
            "no dependency on a hax library crate was found in any "
            f"`Cargo.toml` under {project_root}. Expected one of: "
            f"{', '.join(sorted(crates))}."
        )

    verify(project_root, crates)


if __name__ == "__main__":
    main()
