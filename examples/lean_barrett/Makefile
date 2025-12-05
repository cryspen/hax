.PHONY: default clean
default:
	cargo hax into lean
	(cd proofs/lean && \
   elan default stable && \
   lake build)

clean:
	-rm -f proofs/lean/extraction/lean_barrett.lean
	-cd proofs/lean && lake clean
