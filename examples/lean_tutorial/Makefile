.PHONY: default lean clean

default: lean

lean:
	cargo hax into lean
	(cd proofs/lean && \
		elan default v4.31.0 && \
		lake exe cache get && \
		lake build)

clean:
	-rm -rf proofs/lean/LeanTutorial/Extraction
	-cd proofs/lean && lake clean
