# Build charon's `charon-portable` binary while skipping its `cargo test`
# check phase.
#
# Why this exists: the upstream `#charon-portable` flake output runs charon's
# full test suite as the derivation's check phase. Two of those tests (`toml`
# and `error-dependencies`) make charon spawn a fresh `cargo` to compile test
# crates that pull in dependencies. That works in charon's own CI but fails in
# our build sandbox with `Permission denied (os error 13)` (no network /
# read-only store), breaking the whole derivation. Those tests do not reflect a
# real charon defect for how we use it — our extraction (`make lean`) runs
# charon on the CI runner, outside any sandbox — so we reproduce the portable
# output here with `doCheck = false`.
#
# Usage:
#   nix build --impure --expr \
#     "import ./nix/charon-portable-nocheck.nix { rev = \"$CHARON_REV\"; }"
{ rev
, system ? "x86_64-linux"
}:
let
  charonFlake = builtins.getFlake "github:AeneasVerif/charon/${rev}";
  pkgs = charonFlake.inputs.nixpkgs.legacyPackages.${system};

  # `charon-unwrapped` is the non-store-path-hardcoded charon used to build the
  # upstream `charon-portable`; override it to skip the test check phase.
  unwrapped = charonFlake.packages.${system}.charon-unwrapped.overrideAttrs (_: {
    doCheck = false;
  });
in
# Mirror upstream `charon-portable`: patchelf the binaries to the standard
# loader so they run on a plain Linux runner after a binary-cache hit (when the
# nix store is gone). See the ci.yml note on the `*-portable` outputs.
pkgs.runCommand "charon-portable" { } ''
  mkdir -p $out/bin
  cp ${unwrapped}/bin/charon $out/bin/charon
  cp ${unwrapped}/bin/charon-driver $out/bin/charon-driver

  for f in $out/bin/*; do
    chmod +w $f
    ${pkgs.patchelf}/bin/patchelf --set-interpreter /lib64/ld-linux-x86-64.so.2 $f || true
    ${pkgs.patchelf}/bin/patchelf --remove-rpath $f || true
  done
''
