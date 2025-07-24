use syn::{Ident, PathArguments};

/// Types that we recognize.
#[derive(Clone)]
pub enum Ty {
    /// A vector
    Vec(Box<Ty>),
    /// A box
    Box(Box<Ty>),
    /// A tuple
    Tuple(Vec<Ty>),
    /// An identifier
    Ident(Ident),
    /// An irrelevant type
    Erased,
}

impl From<syn::Type> for Ty {
    fn from(ty: syn::Type) -> Self {
        if let syn::Type::Tuple(tuple) = ty {
            return Ty::Tuple(
                tuple
                    .elems
                    .into_iter()
                    .map(|t| Ty::from(t))
                    .collect::<Vec<_>>(),
            );
        }
        let syn::Type::Path(type_path) = ty else {
            unimplemented!("Other types than path types are not supported yet")
        };
        let Some(last) = type_path.path.segments.iter().last() else {
            unimplemented!("Qualified types are not supported, please `use`.")
        };
        let type_args = match &last.arguments {
            PathArguments::AngleBracketed(args) => args
                .args
                .iter()
                .cloned()
                .flat_map(|x| match x {
                    syn::GenericArgument::Type(t) => Some(t),
                    _ => None,
                })
                .collect(),
            _ => vec![],
        };
        match (last.ident.to_string().as_str(), &type_args[..]) {
            ("Vec", [t]) => Ty::Vec(Box::new(Ty::from(t.clone()))),
            ("Box", [t]) => Ty::Box(Box::new(Ty::from(t.clone()))),
            _ => Self::Ident(last.ident.clone()),
        }
    }
}

impl Ty {
    /// Is this type erased?
    fn erased(&self) -> bool {
        matches!(self, Ty::Erased)
    }
    /// Apply `f` repeatdely in every nested type
    fn map(self, f: &impl Fn(Self) -> Self) -> Self {
        f(match self {
            Ty::Vec(ty) => Ty::Vec(Box::new(ty.map(f))),
            Ty::Box(ty) => Ty::Box(Box::new(ty.map(f))),
            Ty::Tuple(items) => {
                let items = items.into_iter().map(|ty| ty.map(f)).collect();
                Ty::Tuple(items)
            }
            ty => ty,
        })
    }
    /// Normalize the type: bubble up erased value to root or nearest tuple.
    /// E.g. `(Erased, Erased)` is reduced to `Erased` while `(T, Erased)` is stuck.
    pub fn norm(self) -> Self {
        self.erase_when(&|ty| match ty {
            Ty::Vec(ty) | Self::Box(ty) => ty.erased(),
            Ty::Tuple(items) => items.into_iter().all(Ty::erased),
            ty => ty.erased(),
        })
    }
    /// Erase type (at any level of nest) when predicate `f` holds
    pub fn erase_when(self, f: &impl Fn(&Self) -> bool) -> Self {
        self.map(&|ty| if f(&ty) { Self::Erased } else { ty })
    }
}
