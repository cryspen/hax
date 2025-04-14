pub use macro_rules_attribute::{apply, attribute_alias};

attribute_alias! {
    #[apply(derive_AST)] = #[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord, ::schemars::JsonSchema, ::serde::Deserialize, ::serde::Serialize)];
    #[apply(derive_AST_base)] = #[derive(Debug, Clone, Hash, Eq, PartialEq, PartialOrd, Ord)];
}
