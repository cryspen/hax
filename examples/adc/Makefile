.PHONY: lean clean
lean:
	cargo hax into lean --aeneas-args="-core-models-lib"
	(cd proofs/lean && \
		elan default v4.30.0-rc2 && \
		lake exe cache get && \
		lake build)

clean:
	-find proofs/lean/Adc/Extraction -type f ! -name FunsExternal.lean -delete
	-cd proofs/lean && lake clean
