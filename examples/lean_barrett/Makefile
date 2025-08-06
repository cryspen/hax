.PHONY: default lean clean
default:
	cargo hax into lean
	cd proofs/lean/extraction && lake build

clean:
	rm -f proofs/lean/extraction/lean_barrett.lean
	cd proofs/lean/extraction && lake clean
