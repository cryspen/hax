//! The F* backend. The F* printer is still implemented in Ocaml but the phase driver uses this infrastructure

use std::rc::Rc;

use crate::attributes::LinkedItemGraph;

use super::prelude::*;
use hax_rust_engine_macros::setup_printer_struct;
use hax_types::cli_options::{BackendOptions, FStarOptions};

/// The F* backend
pub struct FStarBackend(pub FStarOptions<()>);

/// The Lean printer
#[setup_printer_struct]
#[derive(Clone)]
pub struct LegacyPrinter(BackendOptions<()>);

// TODO this makes no sense, ideally the Printer trait would not require it
impl Default for LegacyPrinter {
    fn default() -> Self {
        Self(
            BackendOptions {
                backend: hax_types::cli_options::Backend::Coq,
                dry_run: false,
                verbose: 0,
                stats: false,
                profile: false,
                prune_haxmeta: None,
                debug_engine: None,
                extract_type_aliases: false,
                translation_options: hax_types::cli_options::TranslationOptions {
                    include_namespaces: Vec::new(),
                },
                output_dir: None,
                cli_extension: hax_types::cli_options::extension::EmptyArgsExtension {},
            },
            Default::default(),
            Default::default(),
        )
    }
}

impl Printer for LegacyPrinter {
    fn resugaring_phases() -> Vec<Box<dyn Resugaring>> {
        vec![]
    }
}

impl<A: 'static + Clone> PrettyAst<A> for LegacyPrinter {
    const NAME: &'static str = "Legacy printer";
    fn module(&self, module: &Module) -> DocBuilder<A> {
        let items = module.items.clone();

        let query = crate::ocaml_engine::QueryKind::Print {
            printer: self.0.backend.clone(),
            input: items,
        };

        let Some(crate::ocaml_engine::Response::Printed(content)) = query.execute(None) else {
            panic!()
        };
        use pretty::docs;
        docs![&pretty::BoxAllocator, content]
    }
}

impl Backend for FStarBackend {
    // TODO Replace by an empty printer
    // This is a dummy value. The fstar backend's printer is implemented in OCaml
    type Printer = LegacyPrinter;

    fn module_path(&self, _module: &Module) -> camino::Utf8PathBuf {
        camino::Utf8PathBuf::from("hello.fst")
    }
    fn printer(&self, linked_item_graph: Rc<LinkedItemGraph>) -> Self::Printer {
        LegacyPrinter(
            BackendOptions {
                backend: hax_types::cli_options::Backend::Fstar(self.0.clone()),
                dry_run: false,
                verbose: 0,
                stats: false,
                profile: false,
                prune_haxmeta: None,
                debug_engine: None,
                extract_type_aliases: false,
                translation_options: hax_types::cli_options::TranslationOptions {
                    include_namespaces: Vec::new(),
                },
                output_dir: None,
                cli_extension: hax_types::cli_options::extension::EmptyArgsExtension {},
            },
            Default::default(),
            linked_item_graph,
        )
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
