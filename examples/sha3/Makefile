.PHONY: default clean
default:
	cargo hax into aeneas-lean --aeneas-args="-core-models-lib"
	
	# Fix for https://github.com/cryspen/aeneas/issues/16
	sed -i 's/(implementation.theta.post st res).holds/(implementation.theta.post st res.swap).holds/' proofs/aeneas-lean/Sha3/Extraction/Specs.lean
	
	(cd proofs/aeneas-lean && \
		elan default v4.30.0-rc2 && \
		lake exe cache get && \
		lake build)

clean:
	-cd proofs/lean && lake clean
