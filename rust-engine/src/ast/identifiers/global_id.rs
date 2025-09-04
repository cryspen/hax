//! The global identifiers of hax.
//!
//! ## Public API
//! The main type provided by this module is `GlobalId`.
//!
//! A global identifier is either:
//!  - a concrete identifier, something that could be represented as a Rust path
//!  - a tuple identifier
//!
//! To print a global identifier, you have to use the method [`GlobalId::view`],
//! which will output a [`view::View`].
//!
//! You can also try to interpret a global identifier as a tuple identifier
//! ([`TupleId`]) via the method [`GlobalId::expect_tuple`].
//!
//! ## Internal representations
//! [`GlobalId`] is a wrapper for an interned [`GlobalIdInner`].
//!
//! A [`GlobalIdInner`] is either a [`ConcreteId`] or a [`TupleId`]. A
//! [`GlobalId`] can always be turned into a [`ConcreteId`].
//!
//! A [`ConcreteId`] is an [`ExplicitDefId`] that can be moved to fresh
//! namespaces or suffixed with reserved suffixes.
//!
//! An [`ExplicitDefId`] is a [`DefId`] that adds one piece of information: is
//! the identifier refering to a constructor or not. This information is
//! ambiguous in Rust's `DefId`s.
//!
//! A [`DefId`] is an interned [`DefIdInner`], which in turn is a datatype
//! isomorphic to the raw representation of `DefId`s in the frontend.
//!
//! A [`DefIdInner`] is basically a definition kind, a krate name and a path.

use hax_frontend_exporter::{DefKind, DefPathItem, DisambiguatedDefPathItem};
use hax_rust_engine_macros::*;

use crate::interning::{Internable, Interned, InterningTable};

mod compact_serialization;
pub(crate) mod generated_names;
pub mod view;

/// A Rust `DefId`: a lighter version of [`hax_frontend_exporter::DefId`].
#[derive_group_for_ast]
struct DefIdInner {
    /// The crate of the definition
    krate: String,
    /// The full path for this definition, under the crate `krate`
    path: Vec<DisambiguatedDefPathItem>,
    /// The parent `DefId`, if any.
    /// `parent` if node if and only if `path` is empty
    parent: Option<DefId>,
    /// What kind is this definition? (e.g. an `enum`, a `const`, an assoc. `fn`...)
    kind: DefKind,
}

impl DefIdInner {
    fn to_debug_string(&self) -> String {
        fn disambiguator_suffix(disambiguator: u32) -> String {
            if disambiguator == 0 {
                "".into()
            } else {
                format!("__{disambiguator}")
            }
        }
        use itertools::Itertools;
        std::iter::once(self.krate.clone())
            .chain(self.path.iter().map(|item| match &item.data {
                DefPathItem::TypeNs(s)
                | DefPathItem::ValueNs(s)
                | DefPathItem::MacroNs(s)
                | DefPathItem::LifetimeNs(s) => s.clone(),
                DefPathItem::Impl => "impl".into(),
                other => format!("{other:?}"),
            } + &disambiguator_suffix(item.disambiguator)))
            .join("::")
    }
}

use std::{
    cell::{LazyCell, RefCell},
    collections::HashMap,
    sync::{LazyLock, Mutex},
};
impl Internable for DefIdInner {
    fn interning_table() -> &'static Mutex<InterningTable<Self>> {
        static TABLE: LazyLock<Mutex<InterningTable<DefIdInner>>> =
            LazyLock::new(|| Mutex::new(InterningTable::default()));
        &TABLE
    }
}

/// An interned Rust `DefId`: a lighter version of [`hax_frontend_exporter::DefId`].
type DefId = Interned<DefIdInner>;

/// An [`ExpliciDefId`] is a Rust [`DefId`] tagged withg some disambiguation metadata.
///
/// [`DefId`] can be ambiguous, consider the following Rust code:
///
/// ```rust
/// struct S;
/// fn f() -> S { S }
/// ```
///
/// Here, the return type of `f` (that is, `S`) and the constructor `S` in the body of `f` refer to the exact same identifier `mycrate::S`.
/// Yet, they denote two very different objects: a type versus a constructor.
///
/// [`ExplicitDefId`] clears up this ambiguity, making constructors and types two separate things.
///
/// Also, an [`ExplicitDefId`] always points to an item: an [`ExplicitDefId`] is never pointing to a crate alone.
#[derive_group_for_ast]
struct ExplicitDefId {
    /// Is this `DefId` a constructor?
    is_constructor: bool,
    /// The `DefId` itself
    def_id: DefId,
}

impl ExplicitDefId {
    /// Get the parent of an `ExplicitDefId`.
    fn parent(&self) -> Option<Self> {
        let def_id = &self.def_id;
        let is_constructor = matches!(&def_id.kind, DefKind::Field);
        Some(Self {
            is_constructor,
            def_id: def_id.parent?,
        })
    }
    /// Returns an iterator that yields `self`, then `self.parent()`, etc.
    /// This iterator is non-empty.
    fn parents(&self) -> impl Iterator<Item = Self> {
        std::iter::successors(Some(self.clone()), |id| id.parent())
    }

    /// Helper to get a `GlobalIdInner` out of an `ExplicitDefId`.
    fn into_global_id_inner(self) -> GlobalIdInner {
        GlobalIdInner::Concrete(ConcreteId {
            def_id: self,
            moved: None,
            suffix: None,
        })
    }
}

/// Represents a fresh module: a module generated by hax and guaranteed to be fresh.
#[derive_group_for_ast]
pub struct FreshModule {
    /// Internal (unique) identifier
    id: usize,
    /// Non-empty list of identifiers that will be used to decide the name of the fresh module.
    hints: Vec<ExplicitDefId>,
    /// A decoration label that will be also used to decide the name of the fresh module.
    label: String,
}

/// [`ReservedSuffix`] helps at deriving fresh identifiers out of existing (Rust) ones.
#[derive_group_for_ast]
pub enum ReservedSuffix {
    /// Precondition of a function-like item.
    Pre,
    /// Postcondition of a function-like item.
    Post,
    /// Cast function for an `enum` discriminant.
    Cast,
}

/// A identifier that we call concrete: it exists concretely somewhere in Rust.
#[derive_group_for_ast]
pub struct ConcreteId {
    /// The explicit `def_id`.
    def_id: ExplicitDefId,
    /// A fresh module if this definition was moved to a fresh module.
    moved: Option<FreshModule>,
    /// An optional suffix.
    suffix: Option<ReservedSuffix>,
}

/// A global identifier in hax.
#[derive_group_for_ast]
enum GlobalIdInner {
    /// A concrete identifier that exists in Rust.
    Concrete(ConcreteId),
    /// A projector.
    Tuple(TupleId),
}

#[derive_group_for_ast]
#[derive(Copy)]
/// Represents tuple-related identifier in Rust.
///
/// Since Rust tuples do not have user-defined names, this type is used to
/// represent synthesized identifiers for tuple types, their constructors, and
/// fields. This is necessary in cases where we need to refer to these
/// components in a structured and identifiable way.
///
/// For ergnomic purposes, `TupleId` can be transformed into `ConcreteId`s.
/// After such a conversion, we loose structure, but we end up with a standard
/// concrete identifier, which can be printed in a generic way.
/// See [`ConcreteId::from_global_id`].
pub enum TupleId {
    /// Represents a tuple type with the given number of elements.
    ///
    /// For example, a tuple like `(i32, bool, String)` would have `length = 3`.
    Type {
        /// Number of elements in the tuple.
        length: usize,
    },

    /// Represents the constructor function for a tuple with the given arity.
    ///
    /// This refers to the tuple expression itself (e.g., `(x, y, z)`), which constructs
    /// a value of the tuple type.
    Constructor {
        /// Number of elements in the tuple.
        length: usize,
    },

    /// Represents a field within a tuple, addressed by position.
    ///
    /// For instance, accessing `.0` or `.1` on a tuple corresponds to a specific field.
    Field {
        /// Number of elements in the tuple.
        length: usize,
        /// Index of the field (zero-based).
        field: usize,
    },
}

impl From<TupleId> for GlobalId {
    fn from(tuple_id: TupleId) -> Self {
        Self(GlobalIdInner::Tuple(tuple_id).intern())
    }
}

impl From<TupleId> for ConcreteId {
    fn from(value: TupleId) -> Self {
        fn patch_def_id(template: GlobalId, length: usize, field: usize) -> ConcreteId {
            let GlobalIdInner::Concrete(mut concrete_id) = template.0.get().clone() else {
                // `patch_def_id` is called with constant values (`hax::Tuple2`
                // and friends are constants) Those are of the shape
                // `GlobalIdInner::Concrete(_)`, *not*
                // `GlobalIdInner::Tuple(_)`. The tuple identifiers we deal with
                // in this functions are private identifiers used only in this
                // module, to provide normal concrete identifiers even for
                // tuples.
                unreachable!()
            };
            fn inner(did: &mut DefIdInner, length: usize, field: usize) {
                for DisambiguatedDefPathItem { data, .. } in &mut did.path {
                    // Patch field
                    if let DefPathItem::ValueNs(s) = data
                        && s == "1"
                    {
                        *s = field.to_string()
                    }
                    // Patch constructor / type name
                    if let DefPathItem::TypeNs(s) = data
                        && s.starts_with("Tuple")
                    {
                        *s = format!("Tuple{length}")
                    }
                }
                if let Some(parent) = did.parent {
                    let mut parent = parent.get().clone();
                    inner(&mut parent, length, field);
                    did.parent = Some(parent.intern());
                }
            }
            let mut did = concrete_id.def_id.def_id.get().clone();
            inner(&mut did, length, field);
            concrete_id.def_id.def_id = did.intern();
            concrete_id
        }

        use crate::names::rust_primitives::hax;

        match value {
            TupleId::Type { length } => patch_def_id(hax::Tuple2, length, 0),
            TupleId::Constructor { length } => patch_def_id(hax::Tuple2::Constructor, length, 0),
            TupleId::Field { length, field } => patch_def_id(hax::Tuple2::_1, length, field),
        }
    }
}

/// A interned global identifier in hax.
#[derive_group_for_ast]
#[derive(Copy)]
pub struct GlobalId(Interned<GlobalIdInner>);

impl GlobalId {
    /// Extracts the Crate info
    pub fn krate(self) -> &'static str {
        &ConcreteId::from_global_id(self).def_id.def_id.krate
    }

    /// Returns true if this global identifier refers to a anonymous constant item.
    /// TODO: drop this function. No logic should be derived from this.
    pub fn is_anonymous_const(self) -> bool {
        let def_id = self.0.get().def_id();
        let Some(DisambiguatedDefPathItem {
            data: DefPathItem::ValueNs(s),
            ..
        }) = def_id.path.last()
        else {
            return false;
        };
        matches!(self.0.get().def_id().kind, DefKind::Const) && s == "_"
    }

    /// Debug printing of identifiers, for testing purposes only.
    /// Prints path in a Rust-like way, as a `::` separated dismabiguated path.
    pub fn to_debug_string(self) -> String {
        ConcreteId::from_global_id(self).to_debug_string()
    }

    /// Returns true if the underlying identifier is a constructor
    pub fn is_constructor(self) -> bool {
        self.0.get().is_constructor()
    }

    /// Returns true if the underlying identifier is a projector
    pub fn is_projector(self) -> bool {
        self.0.get().is_projector()
    }

    /// Returns true if the underlying identifier is a precondition (trait/impl item)
    /// Should be removed once https://github.com/cryspen/hax/issues/1646 has been fixed
    pub fn is_precondition(self) -> bool {
        self.0.get().is_precondition()
    }

    /// Returns true if the underlying identifier is a postcondition (trait/impl item)
    /// Should be removed once https://github.com/cryspen/hax/issues/1646 has been fixed
    pub fn is_postcondition(self) -> bool {
        self.0.get().is_postcondition()
    }

    /// Renders a view of the concrete identifier.
    pub fn view(self) -> view::View {
        ConcreteId::from_global_id(self).view()
    }

    /// Returns a tuple identifier if `self` is indeed a tuple.
    pub fn expect_tuple(self) -> Option<TupleId> {
        match self.0.get() {
            GlobalIdInner::Concrete(..) => None,
            GlobalIdInner::Tuple(tuple_id) => Some(*tuple_id),
        }
    }

    /// Gets the closest module only parent identifier, that is, the closest
    /// parent whose path contains only path chunks of kind `DefKind::Mod`.
    pub fn mod_only_closest_parent(self) -> Self {
        let concrete_id = ConcreteId::from_global_id(self).mod_only_closest_parent();
        Self(GlobalIdInner::Concrete(concrete_id).intern())
    }
}

impl GlobalIdInner {
    /// Extract the raw `DefId` from a `GlobalId`.
    /// This should never be used for name printing.
    fn def_id(&self) -> DefId {
        ConcreteId::from_global_id(GlobalId(self.intern()))
            .def_id
            .def_id
    }

    /// Extract the `ExplicitDefId` from a `GlobalId`.
    fn explicit_def_id(&self) -> Option<ExplicitDefId> {
        match self {
            GlobalIdInner::Concrete(concrete_id) => Some(concrete_id.def_id.clone()),
            GlobalIdInner::Tuple(_) => None,
        }
    }

    /// Returns true if the underlying identifier is a constructor
    pub fn is_constructor(&self) -> bool {
        match self {
            GlobalIdInner::Concrete(concrete_id) => concrete_id.def_id.is_constructor,
            GlobalIdInner::Tuple(TupleId::Constructor { .. }) => true,
            _ => false,
        }
    }

    /// Returns true if the underlying identifier is a projector
    pub fn is_projector(&self) -> bool {
        match self {
            GlobalIdInner::Concrete(concrete_id) => {
                matches!(concrete_id.def_id.def_id.get().kind, DefKind::Field)
            }
            GlobalIdInner::Tuple(TupleId::Field { .. }) => true,
            _ => false,
        }
    }

    /// Returns true if the underlying identifier has the precondition suffix
    /// Should be removed once https://github.com/cryspen/hax/issues/1646 has been fixed
    pub fn is_precondition(&self) -> bool {
        matches!(self, GlobalIdInner::Concrete(concrete_id) if matches!(concrete_id.suffix, Some(ReservedSuffix::Pre)))
    }

    /// Returns true if the underlying identifier has the postcondition suffix
    /// Should be removed once https://github.com/cryspen/hax/issues/1646 has been fixed
    pub fn is_postcondition(&self) -> bool {
        matches!(self, GlobalIdInner::Concrete(concrete_id) if matches!(concrete_id.suffix, Some(ReservedSuffix::Post)))
    }

    /// Returns true if the underlying identifier has the precondition suffix
    /// Should be removed once https://github.com/cryspen/hax/issues/1646 has been fixed
    pub fn is_precondition(&self) -> bool {
        match self {
            GlobalId::Concrete(concrete_id) | GlobalId::Projector(concrete_id) => {
                match concrete_id.suffix {
                    Some(ReservedSuffix::Pre) => true,
                    _ => false,
                }
            }
        }
    }

    /// Returns true if the underlying identifier has the postcondition suffix
    /// Should be removed once https://github.com/cryspen/hax/issues/1646 has been fixed
    pub fn is_postcondition(&self) -> bool {
        match self {
            GlobalId::Concrete(concrete_id) | GlobalId::Projector(concrete_id) => {
                match concrete_id.suffix {
                    Some(ReservedSuffix::Post) => true,
                    _ => false,
                }
            }
        }
    }
}

impl ConcreteId {
    /// Renders a view of the concrete identifier.
    fn view(&self) -> view::View {
        self.def_id.clone().into()
    }

    /// Gets the closest module only parent identifier, that is, the closest
    /// parent whose path contains only path chunks of kind `DefKind::Mod`.
    fn mod_only_closest_parent(&self) -> Self {
        let mut parents = self.def_id.parents().collect::<Vec<_>>();
        parents.reverse();
        let def_id = parents
            .into_iter()
            .take_while(|id| matches!(id.def_id.kind, DefKind::Mod))
            .next()
            .expect("Invariant broken: a DefId must always contain at least on `mod` segment (the crate)");
        Self {
            def_id,
            moved: self.moved.clone(),
            suffix: None,
        }
    }

    /// Get a static reference to a `ConcreteId` out of a `GlobalId`.
    /// When a tuple is encountered, the tuple is rendered into a proper Rust name.
    /// This function is memoized, so that we don't recompute Rust names for tuples all the time.
    fn from_global_id(value: GlobalId) -> &'static ConcreteId {
        thread_local! {
            static MEMO: LazyCell<RefCell<HashMap<GlobalId, &'static ConcreteId>>> =
                LazyCell::new(|| RefCell::new(HashMap::new()));
        }

        MEMO.with(|memo| {
            let mut memo = memo.borrow_mut();
            let reference: &'static ConcreteId =
                memo.entry(value).or_insert_with(|| match value.0.get() {
                    GlobalIdInner::Concrete(concrete_id) => concrete_id,
                    GlobalIdInner::Tuple(tuple_id) => {
                        match GlobalIdInner::Concrete((*tuple_id).into()).intern().get() {
                            GlobalIdInner::Concrete(concrete_id) => concrete_id,
                            GlobalIdInner::Tuple(_) => unreachable!(),
                        }
                    }
                });
            reference
        })
    }

    fn to_debug_string(&self) -> String {
        self.def_id.def_id.get().to_debug_string()
    }
}

impl PartialEq<DefId> for GlobalId {
    fn eq(&self, other: &DefId) -> bool {
        if let GlobalIdInner::Concrete(concrete) = self.0.get() {
            &concrete.def_id.def_id == other
        } else {
            false
        }
    }
}
impl PartialEq<GlobalId> for DefId {
    fn eq(&self, other: &GlobalId) -> bool {
        other == self
    }
}

impl PartialEq<ExplicitDefId> for GlobalId {
    fn eq(&self, other: &ExplicitDefId) -> bool {
        self == &other.def_id
    }
}

impl PartialEq<GlobalId> for ExplicitDefId {
    fn eq(&self, other: &GlobalId) -> bool {
        other == &self.def_id
    }
}
