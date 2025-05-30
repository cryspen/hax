#!/bin/bash

# Get the necessary part of the rust repo
git clone --depth 1 --filter=blob:none --no-checkout https://github.com/rust-lang/rust.git
cd rust
git sparse-checkout init --cone
git checkout master
git sparse-checkout set tests/coverage


# Copy the rust files
cd ..
find rust/tests/coverage -type f -name "*.rs" -exec bash -c '
  for file; do
    dest="src/$(dirname "$file" | sed "s|rust/tests/coverage||")"
    mkdir -p "$dest"
    cp -f "$file" "$dest"
  done
' bash {} +

# Cleanup
cargo fmt
rm -rf rust
