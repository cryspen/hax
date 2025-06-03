// // build.rs

// use std::{fs, path::Path};

// use std::collections::HashSet;
// use syn::{
//     parse_file,
//     visit::{self, Visit},
//     visit_mut::{self, VisitMut},
//     File, GenericParam, Generics, Item, ItemEnum, ItemMod, ItemStruct, Lifetime, LifetimeParam,
//     Type, TypePath,
// };

// struct LifetimeCollector {
//     used: HashSet<syn::Ident>,
// }

// impl<'ast> Visit<'ast> for LifetimeCollector {
//     fn visit_lifetime(&mut self, lt: &'ast Lifetime) {
//         // e.g. for a `&'a Foo` or `Option<&'a T>`, this sees `'a`
//         self.used.insert(lt.ident.clone());
//     }

//     // We still want to recurse into nested types (e.g. generic arguments),
//     // so we let the default `visit_type` run for everything else.
//     fn visit_type(&mut self, ty: &'ast Type) {
//         visit::visit_type(self, ty);
//     }
// }

// // ------------------------------------------------------
// // 2) A small helper to prune any [`GenericParam::Lifetime`] from
// //    `generics.params` if its ident is *not* in the `used` set.
// // ------------------------------------------------------
// fn prune_unused_lifetimes(generics: &mut Generics, used: &HashSet<syn::Ident>) {
//     generics.params = generics
//         .params
//         .iter()
//         .cloned()
//         .filter(|param| match param {
//             GenericParam::Lifetime(lf) => used.contains(&lf.lifetime.ident),
//             _ => true, // keep type‐parameters or const‐parameters unchanged
//         })
//         .collect();
// }

// // ------------------------------------------------------
// // 3) The main `VisitMut` that, for each `ItemStruct` or `ItemEnum`:
// //    • scans all of its field‐types to see which lifetimes are actually used
// //    • removes any lifetime‐parameters that never appeared.
// //
// //    Note: If you also have `where`‐clauses referring to those lifetimes,
// //    you would need an extra pass to remove those predicates as well.
// //    Below we only prune the generic‐parameter list.
// // ------------------------------------------------------
// struct RemoveUnusedLifetimes;

// impl VisitMut for RemoveUnusedLifetimes {
//     fn visit_item_struct_mut(&mut self, item_struct: &mut ItemStruct) {
//         // 1) Collect all lifetimes that appear in field types:
//         let mut collector = LifetimeCollector {
//             used: HashSet::new(),
//         };
//         for field in &item_struct.fields {
//             collector.visit_type(&field.ty);
//         }

//         // 2) Prune any lifetime params not in `collector.used`:
//         prune_unused_lifetimes(&mut item_struct.generics, &collector.used);

//         // 3) Recurse into nested items (e.g. potentially inline‐mods, attributes, etc.)
//         visit_mut::visit_item_struct_mut(self, item_struct);
//     }

//     fn visit_item_enum_mut(&mut self, item_enum: &mut ItemEnum) {
//         // 1) Collect all lifetimes that appear in variant‐field types:
//         let mut collector = LifetimeCollector {
//             used: HashSet::new(),
//         };
//         for variant in &item_enum.variants {
//             for field in &variant.fields {
//                 collector.visit_type(&field.ty);
//             }
//         }

//         // 2) Prune any lifetime params not in `collector.used`:
//         prune_unused_lifetimes(&mut item_enum.generics, &collector.used);

//         // 3) Recurse into nested items
//         visit_mut::visit_item_enum_mut(self, item_enum);
//     }
// }

// /// A `VisitMut` that, at every module level (including the top‐level `File`),
// /// retains only `Item::Struct`, `Item::Enum`, and `Item::Type`, removing all other items.
// struct KeepStructsEnumsTyAliases;

// impl VisitMut for KeepStructsEnumsTyAliases {
//     fn visit_file_mut(&mut self, file: &mut File) {
//         // First, recurse into nested items (modules) so that inner modules get pruned as well.
//         // We need to visit each item before we potentially drop it.
//         for item in &mut file.items {
//             visit_mut::visit_item_mut(self, item);
//         }
//         // Now filter the top‐level items:
//         file.items.retain(|item| {
//             matches!(
//                 item,
//                 Item::Struct(_) | Item::Enum(_) | Item::Type(_) // If you also want to keep `mod foo;` (extern modules) you could add:
//                                                                 // | Item::Mod(ItemMod { content: None, .. })
//             )
//         });
//     }

//     fn visit_item_mod_mut(&mut self, item_mod: &mut ItemMod) {
//         // If this is an inline module (`mod foo { ... }`), then `content` is `Some((brace, Vec<Item>))`.
//         if let Some((_, items)) = &mut item_mod.content {
//             // First recurse into each child item:
//             for child in items.iter_mut() {
//                 visit_mut::visit_item_mut(self, child);
//             }
//             // Then filter this module’s items to keep only Struct, Enum, or Type.
//             items.retain(|child| matches!(child, Item::Struct(_) | Item::Enum(_) | Item::Type(_)));
//         }
//         // If `content` is `None`, it’s an external module (`mod foo;`)—we’ll leave it as is,
//         // but note that it doesn’t contain inline items to filter.
//     }
// }

// /// Visitor #1: For every `TypePath` whose `path` has exactly one segment,
// /// rewrite it to `origin::Segment`.
// ///
// /// e.g. `Expr`     → `origin::Expr`
// ///      `Vec<Expr>` → `origin::Vec<Expr>`
// ///      `Option<T>` → `origin::Option<T>`
// ///
// // Note: this does *not* distinguish between built‐in generics and user‐declared types.
// struct PrefixOrigin;

// impl VisitMut for PrefixOrigin {
//     fn visit_type_path_mut(&mut self, type_path: &mut TypePath) {
//         // Only rewrite if there is no qualified self (`qself`) and exactly one segment.
//         if type_path.qself.is_none() && type_path.path.segments.len() == 1 {
//             // let seg = type_path.path.segments[0].ident.clone();
//             // // Rebuild the path as `origin::ident`
//             // let new_path: TypePath = syn::parse_quote!(origin::#seg);
//             // // But we must preserve any generic arguments on the segment.
//             // // The above parse_quote!(origin::#seg) loses the old arguments,
//             // // so we manually re–attach them.
//             // let orig_args = type_path.path.segments[0].arguments.clone();
//             // let mut rebuilt = new_path.clone();
//             // if let Some(last) = rebuilt.path.segments.last_mut() {
//             //     last.arguments = orig_args;
//             // }
//             type_path
//                 .path
//                 .segments
//                 .insert(0, syn::parse_quote! {origin});
//         }

//         // Continue recursing into nested types (e.g. inside generic args).
//         visit_mut::visit_type_path_mut(self, type_path);
//     }
// }

// /// Visitor #2: For every struct or enum, add a lifetime parameter `'a`
// /// and replace each field‐type `T` with `Value<'a, origin::T>`.
// ///
// /// In detail:
// /// 1) Insert `'a` at the front of the item's `generics`.
// /// 2) For each field in a named‐field struct or in each variant of an enum,
// ///    clone the original type, run `PrefixOrigin` on that clone, then set the
// ///    field’s `ty` to `Value<'a, <that cloned-and–prefixed type>>`.
// ///
// struct WrapValue;

// impl VisitMut for WrapValue {
//     fn visit_item_struct_mut(&mut self, item_struct: &mut ItemStruct) {
//         // 1) Add `'a` to the struct’s generics.
//         let lifetime_param: LifetimeParam = syn::parse_quote!('a);
//         item_struct
//             .generics
//             .params
//             .insert(0, GenericParam::Lifetime(lifetime_param));

//         // 2) For each field, wrap and prefix.
//         for field in &mut item_struct.fields {
//             let orig_ty: Type = field.ty.clone();
//             // Clone and prefix
//             let mut prefixed = orig_ty.clone();
//             PrefixOrigin.visit_type_mut(&mut prefixed);

//             // Build `Value<'a, PrefixedType>`
//             let wrapped: Type = syn::parse_quote!(Value<'a, #prefixed>);
//             field.ty = wrapped;
//         }

//         // Continue into any nested items (though structs rarely nest).
//         visit_mut::visit_item_struct_mut(self, item_struct);
//     }

//     fn visit_item_enum_mut(&mut self, item_enum: &mut ItemEnum) {
//         // 1) Add `'a` to the enum’s generics.
//         let lifetime_param: LifetimeParam = syn::parse_quote!('a);
//         item_enum
//             .generics
//             .params
//             .insert(0, GenericParam::Lifetime(lifetime_param));

//         // 2) For each variant, process each field similarly.
//         for variant in &mut item_enum.variants {
//             for field in &mut variant.fields {
//                 let orig_ty: Type = field.ty.clone();
//                 // Clone and prefix
//                 let mut prefixed = orig_ty.clone();
//                 PrefixOrigin.visit_type_mut(&mut prefixed);

//                 // Build `Value<'a, PrefixedType>`
//                 let wrapped: Type = syn::parse_quote!(Value<'a, #prefixed>);
//                 field.ty = wrapped;
//             }
//         }

//         // Continue recursing.
//         visit_mut::visit_item_enum_mut(self, item_enum);
//     }
// }

fn main() {
    //     let src_path = Path::new("src/ast.rs");
    //     let contents = fs::read_to_string(&src_path).expect("Failed to read src/ast.rs");

    //     let mut ast: File = parse_file(&contents).expect("Failed to parse src/ast.rs as a Rust file");
    //     PrefixOrigin.visit_file_mut(&mut ast);
    //     WrapValue.visit_file_mut(&mut ast);
    //     KeepStructsEnumsTyAliases.visit_file_mut(&mut ast);
    //     RemoveUnusedLifetimes.visit_file_mut(&mut ast);

    //     ast.attrs = vec![];

    //     let formatted = prettyplease::unparse(&ast);
    //     let out_path = Path::new("src/generic_printer/generated.rs");
    //     fs::write(&out_path, formatted).expect("Failed to write generated.rs");
}
