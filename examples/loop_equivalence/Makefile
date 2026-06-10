.PHONY: default clean
default:
	cargo hax into aeneas-lean --aeneas-args="-core-models-lib"
	sed -i \
		'/^open Aeneas /c\open core_models Aeneas\nopen Aeneas.Std hiding namespace core alloc\nopen Result ControlFlow Error' \
		proofs/aeneas-lean/LoopEquivalence/Extraction/Funs.lean
	sed -i \
		's/import Aeneas/import CoreModels/' \
		proofs/aeneas-lean/LoopEquivalence/Extraction/Funs.lean
	(cd proofs/aeneas-lean && \
   elan default v4.30.0-rc2 && \
   lake exe cache get && \
   lake build)

clean:
	-cd proofs/aeneas-lean && lake clean
