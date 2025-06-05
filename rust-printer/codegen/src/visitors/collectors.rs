use std::collections::HashSet;
use syn::{
    visit::{self, Visit},
    Lifetime, Type,
};

#[derive(Default)]
pub struct LifetimeCollector {
    pub used: HashSet<syn::Ident>,
}

impl<'ast> Visit<'ast> for LifetimeCollector {
    fn visit_lifetime(&mut self, lt: &'ast Lifetime) {
        self.used.insert(lt.ident.clone());
    }

    fn visit_type(&mut self, ty: &'ast Type) {
        visit::visit_type(self, ty);
    }
}

#[derive(Default)]
pub struct DatatypeIdentCollector {
    pub idents: HashSet<syn::Ident>,
}

impl<'ast> Visit<'ast> for DatatypeIdentCollector {
    fn visit_item_struct(&mut self, i: &'ast syn::ItemStruct) {
        self.idents.insert(i.ident.clone());
    }
    fn visit_item_enum(&mut self, i: &'ast syn::ItemEnum) {
        self.idents.insert(i.ident.clone());
    }
}
