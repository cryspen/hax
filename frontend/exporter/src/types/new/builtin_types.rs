use crate::prelude::*;

use rustc_middle::ty;
use rustc_span::def_id::DefId as RDefId;

/// We generate fake struct-like items for each of: arrays, slices, and tuples. This makes it
/// easier to emit trait impls for these types, especially with monomorphization. This enum tracks
/// identifies these builtin types.
#[derive(Debug, Hash, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum BuiltinType {
    /// The `[T; N]` type.
    Array,
    /// The `[T]` typ.
    Slice,
    /// The length-n tuple `(A, B, ...)`.
    Tuple(usize),
}

impl<'tcx> GlobalCache<'tcx> {
    pub fn get_builtin_def_id(&mut self, s: &impl BaseState<'tcx>, builtin: BuiltinType) -> RDefId {
        use rustc_hir::definitions::DisambiguatorState;
        use rustc_span::DUMMY_SP;
        use rustc_span::Symbol;
        use rustc_type_ir::Upcast;
        if let Some(def_id) = self.def_ids_of_builtins.get(&builtin) {
            return *def_id;
        }
        let tcx = s.base().tcx;
        let mut disambiguator_state = DisambiguatorState::new();

        let name = match builtin {
            BuiltinType::Array => "<array>",
            BuiltinType::Slice => "<slice>",
            BuiltinType::Tuple(n) => &format!("<tuple_{n}>"),
        };
        // Create a fake item, to which we'll assign generics and a param_env, which we can
        // then use to generate the `FullDefKind` we want.
        let feed = tcx.create_def(
            rustc_span::def_id::CRATE_DEF_ID,
            Some(Symbol::intern(name)),
            rustc_hir::def::DefKind::Struct,
            None,
            &mut disambiguator_state,
        );
        let def_id = feed.def_id().to_def_id();
        // Insert the def_ids early so we record them even if we panic later in this function.
        self.reverse_builtin_map.insert(def_id, builtin);
        self.def_ids_of_builtins.insert(builtin, def_id);

        let mut generics = ty::Generics {
            parent: None,
            parent_count: 0,
            own_params: Default::default(),
            param_def_id_to_index: Default::default(),
            has_self: false,
            has_late_bound_regions: None,
        };
        let mut mk_param = |name: &str, def_kind, kind| {
            let name = Symbol::intern(name);
            let param_feed = tcx.create_def(
                feed.def_id(),
                Some(name),
                def_kind,
                None,
                &mut disambiguator_state,
            );
            param_feed.feed_hir(); // Avoid panics on `local_def_id_to_hir_id`.
            let param_def_id = param_feed.def_id().into();
            let index = generics.own_params.len() as u32;
            let param_def = ty::GenericParamDef {
                name,
                def_id: param_def_id,
                index,
                kind,
                pure_wrt_drop: true,
            };
            let arg = tcx.mk_param_from_def(&param_def);
            generics.own_params.push(param_def);
            generics.param_def_id_to_index.insert(param_def_id, index);
            (arg, param_feed)
        };

        let mut clauses = vec![];
        let sized_trait = tcx.lang_items().sized_trait().unwrap();
        match builtin {
            BuiltinType::Array => {
                let (t_arg, _) = mk_param(
                    "T",
                    rustc_hir::def::DefKind::TyParam,
                    ty::GenericParamDefKind::Type {
                        has_default: false,
                        synthetic: false,
                    },
                );
                let (n_arg, n_feed) = mk_param(
                    "N",
                    rustc_hir::def::DefKind::ConstParam,
                    ty::GenericParamDefKind::Const { has_default: false },
                );
                n_feed.type_of(ty::EarlyBinder::bind(tcx.types.usize));

                let item_ty = t_arg.as_type().unwrap();
                let len = n_arg.as_const().unwrap();
                let type_of = ty::Ty::new_array_with_const_len(tcx, item_ty, len);
                feed.type_of(ty::EarlyBinder::bind(type_of));

                let ty_is_sized = ty::TraitRef::new(tcx, sized_trait, [item_ty]);
                clauses.push(ty_is_sized.upcast(tcx));
                let len_is_usize = ty::ClauseKind::ConstArgHasType(len, tcx.types.usize);
                clauses.push(len_is_usize.upcast(tcx));
            }
            BuiltinType::Slice => {
                let (t_arg, _) = mk_param(
                    "T",
                    rustc_hir::def::DefKind::TyParam,
                    ty::GenericParamDefKind::Type {
                        has_default: false,
                        synthetic: false,
                    },
                );

                let item_ty = t_arg.as_type().unwrap();
                let type_of = ty::Ty::new_slice(tcx, item_ty);
                feed.type_of(ty::EarlyBinder::bind(type_of));

                let ty_is_sized = ty::TraitRef::new(tcx, sized_trait, [item_ty]);
                clauses.push(ty_is_sized.upcast(tcx));
            }
            BuiltinType::Tuple(len) => {
                let tys = (0..len).into_iter().map(|i| {
                    let name: String = if i < 26 {
                        format!("{}", (b'A' + i as u8) as char)
                    } else {
                        format!("T{i}")
                    };
                    let (arg, _) = mk_param(
                        &name,
                        rustc_hir::def::DefKind::TyParam,
                        ty::GenericParamDefKind::Type {
                            has_default: false,
                            synthetic: false,
                        },
                    );
                    arg.as_type().unwrap()
                });
                let tys = tcx.arena.alloc_from_iter(tys);

                let type_of = ty::Ty::new_tup(tcx, tys);
                feed.type_of(ty::EarlyBinder::bind(type_of));

                // All types except the last one are sized.
                for ty in tys.iter().rev().skip(1).rev() {
                    let arg: ty::GenericArg = (*ty).into();
                    let ty_is_sized = ty::TraitRef::new(tcx, sized_trait, [arg]);
                    clauses.push(ty_is_sized.upcast(tcx));
                }
            }
        }

        feed.generics_of(generics);
        feed.explicit_predicates_of(ty::GenericPredicates {
            parent: None,
            predicates: tcx
                .arena
                .alloc_from_iter(clauses.iter().map(|cl| (*cl, DUMMY_SP))),
        });
        feed.param_env(ty::ParamEnv::new(
            tcx.mk_clauses_from_iter(clauses.into_iter()),
        ));
        feed.feed_hir();

        def_id
    }
}
