use hax_types::cli_options::{Command, ENV_VAR_OPTIONS_FRONTEND, Options};

use rustc_ast::Crate;
use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface;
use rustc_middle::ty::TyCtxt;
use rustc_span::symbol::Symbol;

/// Wraps a [Callbacks] structure, and injects some cache-related
/// configuration in the `config` phase of rustc
pub struct CallbacksWrapper<'a> {
    pub sub: &'a mut (dyn Callbacks + Send + 'a),
    pub options: Options,
}
impl<'a> Callbacks for CallbacksWrapper<'a> {
    fn config(&mut self, config: &mut interface::Config) {
        let options = self.options.clone();
        config.psess_created = Some(Box::new(move |parse_sess| {
            // Silence the "unexpected cfg" lints.
            parse_sess.check_config.exhaustive_names = false;
            let depinfo = parse_sess.env_depinfo.get_mut();
            depinfo.insert((
                Symbol::intern(ENV_VAR_OPTIONS_FRONTEND),
                Some(Symbol::intern(&serde_json::to_string(&options).unwrap())),
            ));
            depinfo.insert((
                Symbol::intern("HAX_CARGO_CACHE_KEY"),
                std::env::var("HAX_CARGO_CACHE_KEY")
                    .ok()
                    .as_deref()
                    .map(Symbol::intern),
            ));
        }));
        self.sub.config(config)
    }
    fn after_crate_root_parsing<'tcx>(
        &mut self,
        compiler: &interface::Compiler,
        krate: &mut Crate,
    ) -> Compilation {
        self.sub.after_crate_root_parsing(compiler, krate)
    }
    fn after_expansion<'tcx>(
        &mut self,
        compiler: &interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> Compilation {
        self.sub.after_expansion(compiler, tcx)
    }
    fn after_analysis<'tcx>(
        &mut self,
        compiler: &interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> Compilation {
        self.sub.after_analysis(compiler, tcx)
    }
}
