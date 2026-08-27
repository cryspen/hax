.PHONY: lean clean
lean:
	cargo hax extract sha3
	(cd proofs/sha3/lean && \
		elan default v4.31.0 && \
		lake exe cache get && \
		lake build)

clean:
	-cd proofs/sha3/lean && lake clean
