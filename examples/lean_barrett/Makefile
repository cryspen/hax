.PHONY: default lean clean
default: lean
	make -C proofs/fstar/extraction

lean:
	cargo hax into lean

clean:
	rm -f proofs/lean/extraction/lean_barrett.lean
