.PHONY: default fstar rust clean

default: fstar rust
	make -C proofs/fstar/extraction

fstar:
	cargo hax into fstar

rust:
	cargo hax into rust
	cd proofs/rust/extraction
	cargo build

clean:
	rm -f proofs/fstar/extraction/.depend
	rm -f proofs/fstar/extraction/*.fst
	rm -f proofs/rust/extraction/*.rs
