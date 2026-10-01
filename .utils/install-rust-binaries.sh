# Installs the Rust binaries of the workspace with `cargo install`, together
# with the features each of them needs. Meant to be sourced, with the
# repository root as working directory; arguments are passed on to
# `cargo install`.

install_rust_binaries() {
    local path features
    for path in cli/driver cli/cargo-hax engine/names/extract rust-engine; do
        # The OCaml engine's build consumes `hax-export-json-schemas`.
        if [ "$path" = cli/cargo-hax ]; then
            features="--features legacy-engine"
        else
            features=""
        fi
        (
            set -x
            cargo install --locked --path "$path" $features "$@"
        )
    done
}
