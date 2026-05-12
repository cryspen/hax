//! The ProVerif backend.
//!
//! Phase 1 of the port from the legacy OCaml backend (see
//! `engine/backends/proverif/proverif_backend.ml`). At this stage the backend
//! is wired into the Rust engine's dispatch and runs the OCaml phase pipeline,
//! but the printer overrides are not yet ported — most AST nodes still emit the
//! default "unimplemented method" diagnostic. Subsequent commits port the
//! per-node `PrettyAst` methods one by one.

use std::collections::HashSet;
use std::sync::OnceLock;

use super::prelude::*;
use crate::ast::span::Span;
use crate::phase::*;
use camino::Utf8PathBuf;
use hax_types::engine_api::File;

/// The ProVerif printer.
#[setup_printer_struct]
#[derive(Default, Clone)]
pub struct ProVerifPrinter {}

const HEADER: &str = "\
(*****************************************)
(* Preamble                              *)
(*****************************************)

channel c.

fun construct_fail() : bitstring
reduc construct_fail() = fail.

type Option.
fun Some(bitstring): Option [data].
fun None(): Option [data].
letfun Option_err() = let x = construct_fail() in None().

const empty: bitstring.
letfun bitstring_default() = empty.
letfun bitstring_err() = let x = construct_fail() in bitstring_default().

letfun nat_default() = 0.
fun nat_to_bitstring(nat): bitstring.
letfun nat_err() = let x = construct_fail() in nat_default().

letfun bool_default() = false.

";

impl RenderView for ProVerifPrinter {
    fn reserved_keywords() -> &'static HashSet<String> {
        static SET: OnceLock<HashSet<String>> = OnceLock::new();
        SET.get_or_init(|| {
            // Mirrors `ProVerifNamePolicy.reserved_words` in
            // `engine/backends/proverif/proverif_backend.ml`.
            [
                "among", "axiom", "channel", "choice", "clauses", "const", "def", "diff", "do",
                "elimtrue", "else", "equation", "equivalence", "event", "expand", "fail", "for",
                "forall", "foreach", "free", "fun", "get", "if", "implementation", "in",
                "inj-event", "insert", "lemma", "let", "letfun", "letproba", "new", "noninterf",
                "noselect", "not", "nounif", "or", "otherwise", "out", "param", "phase", "pred",
                "proba", "process", "proof", "public vars", "putbegin", "query", "reduc",
                "restriction", "secret", "select", "set", "suchthat", "sync", "table", "then",
                "type", "weaksecret", "yield",
            ]
            .into_iter()
            .map(|s| s.to_string())
            .collect()
        })
    }

    /// The legacy OCaml backend flattens namespaces with `__` (see
    /// `proverif_backend.ml:653-660`).
    fn separator(&self) -> &str {
        "__"
    }
}

impl Printer for ProVerifPrinter {}

impl<A: 'static + Clone> PrettyAst<A> for ProVerifPrinter {
    const NAME: &'static str = "ProVerif";
}

/// The ProVerif backend.
pub struct ProVerifBackend;

impl Backend for ProVerifBackend {
    type Printer = ProVerifPrinter;

    /// Single-file output (`lib.pvl`) — matches the legacy OCaml backend's
    /// behaviour (see `proverif_backend.ml:868-881`).
    fn module_path(&self, _module: &Module) -> Utf8PathBuf {
        Utf8PathBuf::from("lib.pvl")
    }

    /// The phase pipeline mirrors the OCaml `TransformToInputLanguage`
    /// at `engine/backends/proverif/proverif_backend.ml:887-910`.
    fn phases(&self) -> Vec<PhaseKind> {
        use crate::phase::{PhaseKind::*, legacy::LegacyOCamlPhase::*};
        vec![
            RejectUnsafe.into(),
            RejectRawOrMutPointer.into(),
            TransformHaxLibInline.into(),
            SimplifyQuestionMarks.into(),
            AndMutDefsite.into(),
            ReconstructForLoops.into(),
            DirectAndMut.into(),
            RejectArbitraryLhs.into(),
            DropBlocks.into(),
            DropReferences.into(),
            TrivializeAssignLhs.into(),
            HoistSideEffects.into(),
            SimplifyMatchReturn.into(),
            LocalMutation.into(),
            RejectContinue.into(),
            RejectDyn.into(),
            ReorderFields.into(),
            BundleCycles.into(),
            SortItemsNamespaceWise.into(),
            FilterUnprintableItems,
        ]
    }

    fn resugaring_phases() -> Vec<Box<dyn Resugaring>> {
        // Stage 2 adds protocol-aware resugarings (events, queries, processes).
        vec![]
    }

    /// Collapse every module into a single bag of items so the printer emits
    /// one `lib.pvl` file. Matches `proverif_backend.ml:868-881`.
    fn items_to_module(&self, items: Vec<Item>) -> Vec<Module> {
        if items.is_empty() {
            return vec![];
        }
        let module_ident = items[0].ident.mod_only_closest_parent();
        vec![Module {
            ident: module_ident,
            items,
            meta: Metadata {
                span: Span::dummy(),
                attributes: vec![],
            },
        }]
    }

    fn modules_to_files(&self, modules: Vec<Module>, mut printer: Self::Printer) -> Vec<File> {
        if modules.is_empty() {
            return vec![];
        }
        let path = self.module_path(modules.first().unwrap()).to_string();
        let contents = modules
            .into_iter()
            .map(|module: Module| printer.print(module).0)
            .collect::<Vec<String>>()
            .join("\n");
        vec![File {
            path,
            contents: format!("{}{}", HEADER, contents),
            sourcemap: None,
        }]
    }
}
