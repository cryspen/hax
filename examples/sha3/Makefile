.PHONY: lean clean
lean:
	cargo hax into lean
	(cd proofs/lean && \
		elan default v4.30.0-rc2 && \
		lake exe cache get && \
		lake build)

clean:
	-cd proofs/lean && lake clean
