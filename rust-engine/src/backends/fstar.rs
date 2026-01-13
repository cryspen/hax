//! The F* backend. The F* printer is still implemented in Ocaml but the phase driver uses this infrastructure

/// The F* backend
pub struct FStarBackend;

impl super::Backend for FStarBackend {
    // TODO Replace by an empty printer
    // This is a dummy value. The fstar backend's printer is implemented in OCaml
    type Printer = super::lean::LeanPrinter;

    fn module_path(&self, _module: &super::Module) -> camino::Utf8PathBuf {
        todo!("The fstar backend's printer is implemented in OCaml")
    }

    fn phases(&self) -> Vec<crate::phase::PhaseKind> {
        use crate::phase::legacy::LegacyOCamlPhase::*;
        vec![
            RejectRawOrMutPointer.into(),
            RewriteLocalSelf.into(),
            TransformHaxLibInline.into(),
            Specialize.into(),
            DropSizedTrait.into(),
            SimplifyQuestionMarks.into(),
            AndMutDefsite.into(),
            ReconstructAsserts.into(),
            ReconstructForLoops.into(),
            ReconstructWhileLoops.into(),
            DirectAndMut.into(),
            RejectArbitraryLhs.into(),
            DropBlocks.into(),
            DropMatchGuards.into(),
            DropReferences.into(),
            ExplicitConversions.into(),
            TrivializeAssignLhs.into(),
            HoistSideEffects.into(),
            HoistDisjunctivePatterns.into(),
            SimplifyMatchReturn.into(),
            LocalMutation.into(),
            RewriteControlFlow.into(),
            DropReturnBreakContinue.into(),
            FunctionalizeLoops.into(),
            RejectQuestionMark.into(),
            RejectAsPattern.into(),
            TraitsSpecs.into(),
            SimplifyHoisting.into(),
            NewtypeAsRefinement.into(),
            RejectTraitItemDefault.into(),
            BundleCycles.into(),
            ReorderFields.into(),
            SortItems.into(),
        ]
    }
}
