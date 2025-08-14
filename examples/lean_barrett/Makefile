.PHONY: default lean clean
default:
	cargo hax into lean
	cd proofs/lean/extraction && LAKE_NO_CACHE=1 lake --keep-toolchain --no-cache build

clean:
	rm -f proofs/lean/extraction/lean_barrett.lean
	cd proofs/lean/extraction && LAKE_NO_CACHE=1 lake --keep-toolchain --no-cache clean
