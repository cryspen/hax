cargo hax json -o - | cargo run --manifest-path ../Cargo.toml > src/printed.rs

(
    cd src
    mv main.rs main.rs.bak
    mv printed.rs main.rs
)

cargo fmt
