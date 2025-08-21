.PHONY: default clean
default:
	cargo hax into lean
	(cd proofs/lean/extraction && \
   elan default stable && \
   lake update && \
   lake build)

clean:
	-rm -f proofs/lean/extraction/lean_chacha20.lean
