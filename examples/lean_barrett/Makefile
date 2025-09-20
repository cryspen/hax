.PHONY: default clean
default:
	cargo hax into lean
	(cd proofs/lean/extraction && \
   elan default stable && \
   lake build)

clean:
	-rm -f proofs/lean/extraction/lean_barrett.lean
	-rm -f proofs/lean/extraction/lean-toolchain.lean
	-rm -rf proofs/lean/extraction/.lake
	-cd proofs/lean/extraction && lake clean
