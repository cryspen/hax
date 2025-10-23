.PHONY: default clean
default:
	cargo hax into lean
	(cd proofs/lean/extraction && \
   elan default 4.23.0 && \
   lake build)

clean:
	-rm -f proofs/lean/extraction/lean_chacha20.lean
	-cd proofs/lean/extraction && lake clean
