.PHONY: default clean
default:
	cargo hax into lean --aeneas-args="-core-models-lib"
	(cd proofs/lean && \
		elan default v4.30.0-rc2 && \
		lake exe cache get && \
		lake build)

clean:
	-cd proofs/lean && lake clean
