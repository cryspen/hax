use hax_frontend_exporter::state::LocalContextS;
use hax_frontend_exporter::SInto;
use hax_types::cli_options::{Backend, PathOrDash, ENV_VAR_OPTIONS_FRONTEND};
use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface;
use rustc_interface::interface::Compiler;
use rustc_middle::middle::region::Scope;
use rustc_middle::ty::TyCtxt;
use rustc_middle::{
    thir,
    thir::{Block, BlockId, Expr, ExprId, ExprKind, Pat, PatKind, Stmt, StmtId, StmtKind, Thir},
};
use rustc_span::symbol::Symbol;
use serde::Serialize;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

type ThirBundle<'tcx> = (Rc<rustc_middle::thir::Thir<'tcx>>, ExprId);
/// Generates a dummy THIR body with an error literal as first expression
fn dummy_thir_body(
    tcx: TyCtxt<'_>,
    span: rustc_span::Span,
    guar: rustc_errors::ErrorGuaranteed,
) -> ThirBundle<'_> {
    use rustc_middle::thir::*;
    let ty = tcx.mk_ty_from_kind(rustc_type_ir::TyKind::Never);
    let mut thir = Thir::new(BodyTy::Const(ty));
    let lit_err = tcx.hir_arena.alloc(rustc_span::source_map::Spanned {
        node: rustc_ast::ast::LitKind::Err(guar),
        span: rustc_span::DUMMY_SP,
    });
    let expr = thir.exprs.push(Expr {
        kind: ExprKind::Literal {
            lit: lit_err,
            neg: false,
        },
        ty,
        temp_lifetime: TempLifetime {
            temp_lifetime: None,
            backwards_incompatible: None,
        },
        span,
    });
    (Rc::new(thir), expr)
}

/// Precompute all THIR bodies in a certain order so that we avoid
/// stealing issues (theoretically...)
fn precompute_local_thir_bodies(
    tcx: TyCtxt<'_>,
) -> impl Iterator<Item = (rustc_hir::def_id::DefId, ThirBundle<'_>)> {
    use rustc_hir::def::DefKind::*;
    use rustc_hir::*;

    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
    enum ConstLevel {
        Const,
        ConstFn,
        NotConst,
    }

    #[tracing::instrument(skip(tcx))]
    fn const_level_of(tcx: TyCtxt<'_>, ldid: rustc_span::def_id::LocalDefId) -> ConstLevel {
        let did = ldid.to_def_id();
        if matches!(
            tcx.def_kind(did),
            Const | ConstParam | AssocConst | AnonConst | InlineConst
        ) {
            ConstLevel::Const
        } else if tcx.is_const_fn(ldid.to_def_id()) {
            ConstLevel::ConstFn
        } else {
            ConstLevel::NotConst
        }
    }

    use itertools::Itertools;
    tcx.hir_body_owners()
        .filter(|ldid| match tcx.def_kind(ldid.to_def_id()) {
            InlineConst | AnonConst => {
                fn is_fn(tcx: TyCtxt<'_>, did: rustc_span::def_id::DefId) -> bool {
                    use rustc_hir::def::DefKind;
                    matches!(
                        tcx.def_kind(did),
                        DefKind::Fn | DefKind::AssocFn | DefKind::Ctor(..) | DefKind::Closure
                    )
                }
                !is_fn(tcx, tcx.local_parent(*ldid).to_def_id())
            }
            _ => true,
        })
        .sorted_by_key(|ldid| const_level_of(tcx, *ldid))
        .filter(move |ldid| tcx.hir_maybe_body_owned_by(*ldid).is_some())
        .map(move |ldid| {
            tracing::debug!("⏳ Type-checking THIR body for {:#?}", ldid);
            let hir_id = tcx.local_def_id_to_hir_id(ldid);
            // The `type_of` anon constants isn't available directly, it needs to be fed by some
            // other query. This hack ensures this happens, otherwise `thir_body` returns an error.
            // See https://rust-lang.zulipchat.com/#narrow/channel/182449-t-compiler.2Fhelp/topic/Change.20in.20THIR.20of.20anonymous.20constants.3F/near/509764021 .
            for (parent_id, parent) in tcx.hir_parent_iter(hir_id) {
                if let rustc_hir::Node::Item(..) = parent {
                    let _ = tcx.check_well_formed(parent_id.owner.def_id);
                    break;
                }
            }
            let span = tcx.hir().span(hir_id);
            let (thir, expr) = match tcx.thir_body(ldid) {
                Ok(x) => x,
                Err(e) => {
                    let guar = tcx.dcx().span_err(
                        span,
                        "While trying to reach a body's THIR defintion, got a typechecking error.",
                    );
                    return (ldid, dummy_thir_body(tcx, span, guar));
                }
            };
            if thir.is_stolen() {
                let guar = tcx.dcx().span_err(
                    span,
                    format!(
                        "The THIR body of item {:?} was stolen.\n\
                        This is not supposed to happen.\n\
                        This is a bug in Hax's frontend.\n\
                        This is discussed in issue https://github.com/hacspec/hax/issues/27.\n\
                        Please comment this issue if you see this error message!",
                        ldid
                    ),
                );
                return (ldid, dummy_thir_body(tcx, span, guar));
            }
            let thir = thir.borrow().clone();
            tracing::debug!("✅ Type-checked THIR body for {:#?}", ldid);
            (ldid, (Rc::new(thir), expr))
        })
        .map(|(ldid, bundle)| (ldid.to_def_id(), bundle))
}

/// Browse a crate and translate every item from HIR+THIR to "THIR'"
/// (I call "THIR'" the AST described in this crate)
#[tracing::instrument(skip_all)]
fn convert_thir<'tcx, Body: hax_frontend_exporter::IsBody>(
    options: &hax_frontend_exporter_options::Options,
    tcx: TyCtxt<'tcx>,
) -> (
    Vec<rustc_span::Span>,
    Vec<hax_frontend_exporter::DefId>,
    Vec<(
        hax_frontend_exporter::DefId,
        hax_frontend_exporter::ImplInfos,
    )>,
    Vec<hax_frontend_exporter::Item<Body>>,
    hax_frontend_exporter::id_table::Table,
) {
    use hax_frontend_exporter::WithGlobalCacheExt;
    let state = hax_frontend_exporter::state::State::new(tcx, options.clone());
    for (def_id, thir) in precompute_local_thir_bodies(tcx) {
        state.with_item_cache(def_id, |caches| caches.thir = Some(thir));
    }

    let result = tcx
        .hir_free_items()
        .map(|id| tcx.hir_item(id).sinto(&state))
        .collect();
    let impl_infos = hax_frontend_exporter::impl_def_ids_to_impled_types_and_bounds(&state)
        .into_iter()
        .collect();
    let exported_spans = state.with_global_cache(|cache| cache.spans.keys().copied().collect());
    let exported_def_ids = state.with_global_cache(|cache| {
        cache
            .per_item
            .values()
            .filter_map(|per_item_cache| per_item_cache.def_id.clone())
            .collect()
    });
    let cache_map = state.with_global_cache(|cache| cache.id_table_session.table().clone());

    (
        exported_spans,
        exported_def_ids,
        impl_infos,
        result,
        cache_map,
    )
}

/// Callback for extraction
#[derive(Debug, Clone, Serialize)]
pub(crate) struct ExtractionCallbacks {
    pub body_types: Vec<hax_types::cli_options::ExportBodyKind>,
}

impl From<ExtractionCallbacks> for hax_frontend_exporter_options::Options {
    fn from(opts: ExtractionCallbacks) -> hax_frontend_exporter_options::Options {
        hax_frontend_exporter_options::Options {
            inline_anon_consts: true,
        }
    }
}

impl Callbacks for ExtractionCallbacks {
    fn after_expansion<'tcx>(&mut self, compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        use std::ops::{Deref, DerefMut};

        use hax_frontend_exporter::ThirBody;
        use hax_types::cli_options::Command;
        use rustc_session::config::CrateType;
        use serde::{Deserialize, Serialize};
        use std::fs::File;
        use std::io::BufWriter;

        use std::path::PathBuf;

        let opts = &compiler.sess.opts;
        let externs: Vec<_> = opts
            .externs
            .iter()
            .flat_map(|(_, ext)| match &ext.location {
                rustc_session::config::ExternLocation::ExactPaths(set) => set
                    .iter()
                    .map(|cp| cp.canonicalized())
                    .collect::<Vec<_>>()
                    .into_iter(),
                _ => vec![].into_iter(),
            })
            .map(|path| path.with_extension("haxmeta"))
            .collect();

        let cg_metadata = opts.cg.metadata[0].clone();
        let crate_name = opts.crate_name.clone().unwrap();

        let output_dir = compiler.sess.io.output_dir.clone().unwrap();
        let haxmeta_path = output_dir.join(format!("{crate_name}-{cg_metadata}.haxmeta",));

        let mut file = BufWriter::new(File::create(&haxmeta_path).unwrap());

        use hax_types::driver_api::{with_kind_type, HaxMeta};
        with_kind_type!(
            self.body_types.clone(),
            <Body>|| {
                let (spans, def_ids, impl_infos, items, cache_map) =
                    convert_thir(&self.clone().into(), tcx);
                let files: HashSet<PathBuf> = HashSet::from_iter(
                    items
                        .iter()
                        .flat_map(|item| item.span.filename.to_path().map(|path| path.to_path_buf()))
                );
                let haxmeta: HaxMeta<Body> = HaxMeta {
                    crate_name,
                    cg_metadata,
                    externs,
                    impl_infos,
                    items,
                    comments: files.into_iter()
                        .flat_map(|path|hax_frontend_exporter::comments::comments_of_file(path).ok())
                        .flatten()
                        .collect(),
                    def_ids,
                    hax_version: hax_types::HAX_VERSION.into(),
                };
                haxmeta.write(&mut file, cache_map);
            }
        );

        let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap();
        let manifest_dir = std::path::Path::new(&manifest_dir);

        let data = hax_types::driver_api::EmitHaxMetaMessage {
            manifest_dir: manifest_dir.to_path_buf(),
            working_dir: opts
                .working_dir
                .to_path(rustc_span::FileNameDisplayPreference::Local)
                .to_path_buf(),
            path: haxmeta_path,
        };
        eprintln!(
            "{}{}",
            hax_types::driver_api::HAX_DRIVER_STDERR_PREFIX,
            &serde_json::to_string(&hax_types::driver_api::HaxDriverMessage::EmitHaxMeta(data))
                .unwrap()
        );

        Compilation::Stop
    }
}
