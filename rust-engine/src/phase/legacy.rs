//! This module exposes the legacy phases written in OCaml in the OCaml engine.

use crate::{ast::Item, phase::Phase};

struct LegacyOCamlPhases {
    phases: Vec<String>,
}

impl Phase for LegacyOCamlPhases {
    fn apply(&self, items: &mut Vec<Item>) {
        eprintln!("Applying phases: {:#?}", &self.phases);
        use crate::ocaml_engine::Response;
        let query = crate::ocaml_engine::QueryKind::ApplyPhases {
            input: std::mem::take(items),
            phases: self.phases.clone(),
        };
        let Some(Response::ApplyPhases { output }) = query.execute(None) else {
            panic!()
        };
        *items = output;
    }

    fn legacy_ocaml_phase(&self) -> Option<&str> {
        match self.phases.as_slice() {
            [phase] => Some(phase.as_str()),
            _ => None,
        }
    }
}

/// Group consecutive ocaml phases as one monolithic phase, so that we avoid extra roundtrips to the OCaml engine.
pub fn group_consecutive_ocaml_phases(phases: Vec<Box<dyn Phase>>) -> Vec<Box<dyn Phase>> {
    let mut output: Vec<Box<dyn Phase>> = vec![];
    let mut ocaml_phases = vec![];
    let mut phases = phases.into_iter();

    loop {
        let phase = phases.next();
        if let Some(ocaml_phase) = phase.as_ref().and_then(|phase| phase.legacy_ocaml_phase()) {
            ocaml_phases.push(ocaml_phase.to_string())
        } else {
            if !ocaml_phases.is_empty() {
                output.push(Box::new(LegacyOCamlPhases {
                    phases: std::mem::take(&mut ocaml_phases),
                }));
            }
            if let Some(phase) = phase {
                output.push(phase);
            } else {
                break;
            }
        }
    }

    output
}

macro_rules! make_ocaml_legacy_phase {
    ($($name:ident),*) => {
        $(
            #[doc = concat!("The phase ", stringify!($name), " from the OCaml engine.")]
            pub fn $name() -> Box<dyn Phase> {
                Box::new(LegacyOCamlPhases {
                    phases: vec![stringify!($name).to_string()],
                })
            }
        )*
    };
}

make_ocaml_legacy_phase!(
    and_mut_defsite,
    bundle_cycles,
    cf_into_monads,
    direct_and_mut,
    drop_blocks,
    drop_match_guards,
    drop_references,
    drop_return_break_continue,
    drop_sized_trait,
    functionalize_loops,
    hoist_disjunctive_patterns,
    local_mutation,
    newtype_as_refinement,
    reconstruct_asserts,
    reconstruct_for_index_loops,
    reconstruct_for_loops,
    reconstruct_question_marks,
    reconstruct_while_loops,
    reorder_fields,
    rewrite_control_flow,
    rewrite_local_self,
    simplify_hoisting,
    simplify_match_return,
    simplify_question_marks,
    sort_items,
    specialize,
    traits_specs,
    transform_hax_lib_inline,
    trivialize_assign_lhs,
    reject_arbitrary_lhs,
    reject_continue,
    reject_question_mark,
    reject_raw_or_mut_pointer,
    reject_early_exit,
    reject_as_pattern,
    reject_dyn,
    reject_trait_item_default,
    reject_unsafe,
    hoist_side_effects
);
