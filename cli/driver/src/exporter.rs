use hax_frontend_exporter::SInto;
use hax_frontend_exporter::state::LocalContextS;
use hax_types::cli_options::{Backend, ENV_VAR_OPTIONS_FRONTEND, PathOrDash};
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
            bounds_options: hax_frontend_exporter_options::BoundsOptions {
                resolve_drop: false,
                prune_sized: true,
            },
        }
    }
}

impl Callbacks for ExtractionCallbacks {
    fn config(&mut self, config: &mut rustc_interface::interface::Config) {
        config.override_queries = Some(|_sess, providers| {
            hax_frontend_exporter::override_queries_store_body(providers);
        });
    }
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

        use hax_types::driver_api::{HaxMeta, with_kind_type};
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
