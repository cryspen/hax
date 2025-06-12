use syn::{
    File, GenericParam, ItemEnum, ItemStruct, LifetimeParam, Type,
    visit_mut::{self, VisitMut},
};

use super::utils;

/// Mutate the type of structs and enums variants fields, effectively transforming them from `T` to `PrintContext<'a, T>`.
/// This takes care of adding a lifetime `'a`.
pub struct WrapTypesWithCtx;

impl VisitMut for WrapTypesWithCtx {
    fn visit_item_struct_mut(&mut self, item_struct: &mut ItemStruct) {
        let lifetime_param: LifetimeParam = syn::parse_quote!('a);
        item_struct
            .generics
            .params
            .insert(0, GenericParam::Lifetime(lifetime_param));
        for field in &mut item_struct.fields {
            let orig_ty: Type = field.ty.clone();
            let mut prefixed = orig_ty.clone();
            utils::PrefixOrigin.visit_type_mut(&mut prefixed);
            let wrapped: Type = syn::parse_quote!(PrintContext<'a, #prefixed>);
            field.ty = wrapped;
        }

        visit_mut::visit_item_struct_mut(self, item_struct);
    }

    fn visit_item_enum_mut(&mut self, item_enum: &mut ItemEnum) {
        let lifetime_param: LifetimeParam = syn::parse_quote!('a);
        item_enum
            .generics
            .params
            .insert(0, GenericParam::Lifetime(lifetime_param));

        for variant in &mut item_enum.variants {
            for field in &mut variant.fields {
                let orig_ty: Type = field.ty.clone();
                let mut prefixed = orig_ty.clone();
                utils::PrefixOrigin.visit_type_mut(&mut prefixed);

                let wrapped: Type = syn::parse_quote!(PrintContext<'a, #prefixed>);
                field.ty = wrapped;
            }
        }

        visit_mut::visit_item_enum_mut(self, item_enum);
    }
}

/// Creates a shallow view of every datatype found in `ast`. This replicates
/// every datatype of `ast`.
///
/// However, we replace every field type `T` by a type `PrintContext<'a, U>`, where `U`
/// is alike `T` but with every subtype of `U` being prefixed by `origin::`.
///
/// For instance, `my_field: Vec<Expr>` becomes `my_field: PrintContext<'a, origin::Vec<origin::Expr>>`.
///
/// Also, we add a lifetime `'a` to each datatype automatically.
pub fn transform_ast_with_contextes(ast: &mut File) {
    utils::PrefixOrigin.visit_file_mut(ast);
    WrapTypesWithCtx.visit_file_mut(ast);
    utils::RemoveUnusedLifetimes.visit_file_mut(ast);
}
