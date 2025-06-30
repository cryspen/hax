//! The `Fragment` type for holding arbitrary AST fragments.
//!
//! This enum is useful for diagnostics or dynamic dispatch on generic AST values.
//! It acts as a type-erased wrapper around various core AST node types.

use crate::ast::*;

impl From<GenericValue> for Fragment {
    fn from(item: GenericValue) -> Self {
        Self::GenericValue(item)
    }
}
impl From<PrimitiveTy> for Fragment {
    fn from(item: PrimitiveTy) -> Self {
        Self::PrimitiveTy(item)
    }
}
impl From<Region> for Fragment {
    fn from(item: Region) -> Self {
        Self::Region(item)
    }
}
impl From<Ty> for Fragment {
    fn from(item: Ty) -> Self {
        Self::Ty(item)
    }
}
impl From<DynTraitGoal> for Fragment {
    fn from(item: DynTraitGoal) -> Self {
        Self::DynTraitGoal(item)
    }
}
impl From<Metadata> for Fragment {
    fn from(item: Metadata) -> Self {
        Self::Metadata(item)
    }
}
impl From<Expr> for Fragment {
    fn from(item: Expr) -> Self {
        Self::Expr(item)
    }
}
impl From<Pat> for Fragment {
    fn from(item: Pat) -> Self {
        Self::Pat(item)
    }
}
impl From<Arm> for Fragment {
    fn from(item: Arm) -> Self {
        Self::Arm(item)
    }
}
impl From<Guard> for Fragment {
    fn from(item: Guard) -> Self {
        Self::Guard(item)
    }
}
impl From<BorrowKind> for Fragment {
    fn from(item: BorrowKind) -> Self {
        Self::BorrowKind(item)
    }
}
impl From<BindingMode> for Fragment {
    fn from(item: BindingMode) -> Self {
        Self::BindingMode(item)
    }
}
impl From<PatKind> for Fragment {
    fn from(item: PatKind) -> Self {
        Self::PatKind(item)
    }
}
impl From<GuardKind> for Fragment {
    fn from(item: GuardKind) -> Self {
        Self::GuardKind(item)
    }
}
impl From<Lhs> for Fragment {
    fn from(item: Lhs) -> Self {
        Self::Lhs(item)
    }
}
impl From<ImplExpr> for Fragment {
    fn from(item: ImplExpr) -> Self {
        Self::ImplExpr(item)
    }
}
impl From<ImplExprKind> for Fragment {
    fn from(item: ImplExprKind) -> Self {
        Self::ImplExprKind(item)
    }
}
impl From<ImplItem> for Fragment {
    fn from(item: ImplItem) -> Self {
        Self::ImplItem(item)
    }
}
impl From<ImplItemKind> for Fragment {
    fn from(item: ImplItemKind) -> Self {
        Self::ImplItemKind(item)
    }
}
impl From<TraitItem> for Fragment {
    fn from(item: TraitItem) -> Self {
        Self::TraitItem(item)
    }
}
impl From<TraitItemKind> for Fragment {
    fn from(item: TraitItemKind) -> Self {
        Self::TraitItemKind(item)
    }
}
impl From<QuoteContent> for Fragment {
    fn from(item: QuoteContent) -> Self {
        Self::QuoteContent(item)
    }
}
impl From<Quote> for Fragment {
    fn from(item: Quote) -> Self {
        Self::Quote(item)
    }
}
impl From<ItemQuoteOrigin> for Fragment {
    fn from(item: ItemQuoteOrigin) -> Self {
        Self::ItemQuoteOrigin(item)
    }
}
impl From<ItemQuoteOriginKind> for Fragment {
    fn from(item: ItemQuoteOriginKind) -> Self {
        Self::ItemQuoteOriginKind(item)
    }
}
impl From<ItemQuoteOriginPosition> for Fragment {
    fn from(item: ItemQuoteOriginPosition) -> Self {
        Self::ItemQuoteOriginPosition(item)
    }
}
impl From<LoopKind> for Fragment {
    fn from(item: LoopKind) -> Self {
        Self::LoopKind(item)
    }
}
impl From<ControlFlowKind> for Fragment {
    fn from(item: ControlFlowKind) -> Self {
        Self::ControlFlowKind(item)
    }
}
impl From<LoopState> for Fragment {
    fn from(item: LoopState) -> Self {
        Self::LoopState(item)
    }
}
impl From<ExprKind> for Fragment {
    fn from(item: ExprKind) -> Self {
        Self::ExprKind(item)
    }
}
impl From<GenericParamKind> for Fragment {
    fn from(item: GenericParamKind) -> Self {
        Self::GenericParamKind(item)
    }
}
impl From<TraitGoal> for Fragment {
    fn from(item: TraitGoal) -> Self {
        Self::TraitGoal(item)
    }
}
impl From<ImplIdent> for Fragment {
    fn from(item: ImplIdent) -> Self {
        Self::ImplIdent(item)
    }
}
impl From<ProjectionPredicate> for Fragment {
    fn from(item: ProjectionPredicate) -> Self {
        Self::ProjectionPredicate(item)
    }
}
impl From<GenericConstraint> for Fragment {
    fn from(item: GenericConstraint) -> Self {
        Self::GenericConstraint(item)
    }
}
impl From<GenericParam> for Fragment {
    fn from(item: GenericParam) -> Self {
        Self::GenericParam(item)
    }
}
impl From<Generics> for Fragment {
    fn from(item: Generics) -> Self {
        Self::Generics(item)
    }
}
impl From<SafetyKind> for Fragment {
    fn from(item: SafetyKind) -> Self {
        Self::SafetyKind(item)
    }
}
impl From<Attribute> for Fragment {
    fn from(item: Attribute) -> Self {
        Self::Attribute(item)
    }
}
impl From<AttributeKind> for Fragment {
    fn from(item: AttributeKind) -> Self {
        Self::AttributeKind(item)
    }
}
impl From<DocCommentKind> for Fragment {
    fn from(item: DocCommentKind) -> Self {
        Self::DocCommentKind(item)
    }
}
impl From<SpannedTy> for Fragment {
    fn from(item: SpannedTy) -> Self {
        Self::SpannedTy(item)
    }
}
impl From<Param> for Fragment {
    fn from(item: Param) -> Self {
        Self::Param(item)
    }
}
impl From<Variant> for Fragment {
    fn from(item: Variant) -> Self {
        Self::Variant(item)
    }
}
impl From<ItemKind> for Fragment {
    fn from(item: ItemKind) -> Self {
        Self::ItemKind(item)
    }
}
impl From<Item> for Fragment {
    fn from(item: Item) -> Self {
        Self::Item(item)
    }
}

/// An owned fragment of the AST: this enumeration can represent any node in the AST.
#[allow(missing_docs)]
#[derive_group_for_ast]
pub enum Fragment {
    GenericValue(GenericValue),
    PrimitiveTy(PrimitiveTy),
    Region(Region),
    Ty(Ty),
    DynTraitGoal(DynTraitGoal),
    Metadata(Metadata),
    Expr(Expr),
    Pat(Pat),
    Arm(Arm),
    Guard(Guard),
    BorrowKind(BorrowKind),
    BindingMode(BindingMode),
    PatKind(PatKind),
    GuardKind(GuardKind),
    Lhs(Lhs),
    ImplExpr(ImplExpr),
    ImplExprKind(ImplExprKind),
    ImplItem(ImplItem),
    ImplItemKind(ImplItemKind),
    TraitItem(TraitItem),
    TraitItemKind(TraitItemKind),
    QuoteContent(QuoteContent),
    Quote(Quote),
    ItemQuoteOrigin(ItemQuoteOrigin),
    ItemQuoteOriginKind(ItemQuoteOriginKind),
    ItemQuoteOriginPosition(ItemQuoteOriginPosition),
    LoopKind(LoopKind),
    ControlFlowKind(ControlFlowKind),
    LoopState(LoopState),
    ExprKind(ExprKind),
    GenericParamKind(GenericParamKind),
    TraitGoal(TraitGoal),
    ImplIdent(ImplIdent),
    ProjectionPredicate(ProjectionPredicate),
    GenericConstraint(GenericConstraint),
    GenericParam(GenericParam),
    Generics(Generics),
    SafetyKind(SafetyKind),
    Attribute(Attribute),
    AttributeKind(AttributeKind),
    DocCommentKind(DocCommentKind),
    SpannedTy(SpannedTy),
    Param(Param),
    Variant(Variant),
    ItemKind(ItemKind),
    Item(Item),
    Unknown(String),
}
impl<'lt> From<&'lt GenericValue> for FragmentRef<'lt> {
    fn from(item: &'lt GenericValue) -> Self {
        Self::GenericValue(item)
    }
}
impl<'lt> From<&'lt PrimitiveTy> for FragmentRef<'lt> {
    fn from(item: &'lt PrimitiveTy) -> Self {
        Self::PrimitiveTy(item)
    }
}
impl<'lt> From<&'lt Region> for FragmentRef<'lt> {
    fn from(item: &'lt Region) -> Self {
        Self::Region(item)
    }
}
impl<'lt> From<&'lt Ty> for FragmentRef<'lt> {
    fn from(item: &'lt Ty) -> Self {
        Self::Ty(item)
    }
}
impl<'lt> From<&'lt DynTraitGoal> for FragmentRef<'lt> {
    fn from(item: &'lt DynTraitGoal) -> Self {
        Self::DynTraitGoal(item)
    }
}
impl<'lt> From<&'lt Metadata> for FragmentRef<'lt> {
    fn from(item: &'lt Metadata) -> Self {
        Self::Metadata(item)
    }
}
impl<'lt> From<&'lt Expr> for FragmentRef<'lt> {
    fn from(item: &'lt Expr) -> Self {
        Self::Expr(item)
    }
}
impl<'lt> From<&'lt Pat> for FragmentRef<'lt> {
    fn from(item: &'lt Pat) -> Self {
        Self::Pat(item)
    }
}
impl<'lt> From<&'lt Arm> for FragmentRef<'lt> {
    fn from(item: &'lt Arm) -> Self {
        Self::Arm(item)
    }
}
impl<'lt> From<&'lt Guard> for FragmentRef<'lt> {
    fn from(item: &'lt Guard) -> Self {
        Self::Guard(item)
    }
}
impl<'lt> From<&'lt BorrowKind> for FragmentRef<'lt> {
    fn from(item: &'lt BorrowKind) -> Self {
        Self::BorrowKind(item)
    }
}
impl<'lt> From<&'lt BindingMode> for FragmentRef<'lt> {
    fn from(item: &'lt BindingMode) -> Self {
        Self::BindingMode(item)
    }
}
impl<'lt> From<&'lt PatKind> for FragmentRef<'lt> {
    fn from(item: &'lt PatKind) -> Self {
        Self::PatKind(item)
    }
}
impl<'lt> From<&'lt GuardKind> for FragmentRef<'lt> {
    fn from(item: &'lt GuardKind) -> Self {
        Self::GuardKind(item)
    }
}
impl<'lt> From<&'lt Lhs> for FragmentRef<'lt> {
    fn from(item: &'lt Lhs) -> Self {
        Self::Lhs(item)
    }
}
impl<'lt> From<&'lt ImplExpr> for FragmentRef<'lt> {
    fn from(item: &'lt ImplExpr) -> Self {
        Self::ImplExpr(item)
    }
}
impl<'lt> From<&'lt ImplExprKind> for FragmentRef<'lt> {
    fn from(item: &'lt ImplExprKind) -> Self {
        Self::ImplExprKind(item)
    }
}
impl<'lt> From<&'lt ImplItem> for FragmentRef<'lt> {
    fn from(item: &'lt ImplItem) -> Self {
        Self::ImplItem(item)
    }
}
impl<'lt> From<&'lt ImplItemKind> for FragmentRef<'lt> {
    fn from(item: &'lt ImplItemKind) -> Self {
        Self::ImplItemKind(item)
    }
}
impl<'lt> From<&'lt TraitItem> for FragmentRef<'lt> {
    fn from(item: &'lt TraitItem) -> Self {
        Self::TraitItem(item)
    }
}
impl<'lt> From<&'lt TraitItemKind> for FragmentRef<'lt> {
    fn from(item: &'lt TraitItemKind) -> Self {
        Self::TraitItemKind(item)
    }
}
impl<'lt> From<&'lt QuoteContent> for FragmentRef<'lt> {
    fn from(item: &'lt QuoteContent) -> Self {
        Self::QuoteContent(item)
    }
}
impl<'lt> From<&'lt Quote> for FragmentRef<'lt> {
    fn from(item: &'lt Quote) -> Self {
        Self::Quote(item)
    }
}
impl<'lt> From<&'lt ItemQuoteOrigin> for FragmentRef<'lt> {
    fn from(item: &'lt ItemQuoteOrigin) -> Self {
        Self::ItemQuoteOrigin(item)
    }
}
impl<'lt> From<&'lt ItemQuoteOriginKind> for FragmentRef<'lt> {
    fn from(item: &'lt ItemQuoteOriginKind) -> Self {
        Self::ItemQuoteOriginKind(item)
    }
}
impl<'lt> From<&'lt ItemQuoteOriginPosition> for FragmentRef<'lt> {
    fn from(item: &'lt ItemQuoteOriginPosition) -> Self {
        Self::ItemQuoteOriginPosition(item)
    }
}
impl<'lt> From<&'lt LoopKind> for FragmentRef<'lt> {
    fn from(item: &'lt LoopKind) -> Self {
        Self::LoopKind(item)
    }
}
impl<'lt> From<&'lt ControlFlowKind> for FragmentRef<'lt> {
    fn from(item: &'lt ControlFlowKind) -> Self {
        Self::ControlFlowKind(item)
    }
}
impl<'lt> From<&'lt LoopState> for FragmentRef<'lt> {
    fn from(item: &'lt LoopState) -> Self {
        Self::LoopState(item)
    }
}
impl<'lt> From<&'lt ExprKind> for FragmentRef<'lt> {
    fn from(item: &'lt ExprKind) -> Self {
        Self::ExprKind(item)
    }
}
impl<'lt> From<&'lt GenericParamKind> for FragmentRef<'lt> {
    fn from(item: &'lt GenericParamKind) -> Self {
        Self::GenericParamKind(item)
    }
}
impl<'lt> From<&'lt TraitGoal> for FragmentRef<'lt> {
    fn from(item: &'lt TraitGoal) -> Self {
        Self::TraitGoal(item)
    }
}
impl<'lt> From<&'lt ImplIdent> for FragmentRef<'lt> {
    fn from(item: &'lt ImplIdent) -> Self {
        Self::ImplIdent(item)
    }
}
impl<'lt> From<&'lt ProjectionPredicate> for FragmentRef<'lt> {
    fn from(item: &'lt ProjectionPredicate) -> Self {
        Self::ProjectionPredicate(item)
    }
}
impl<'lt> From<&'lt GenericConstraint> for FragmentRef<'lt> {
    fn from(item: &'lt GenericConstraint) -> Self {
        Self::GenericConstraint(item)
    }
}
impl<'lt> From<&'lt GenericParam> for FragmentRef<'lt> {
    fn from(item: &'lt GenericParam) -> Self {
        Self::GenericParam(item)
    }
}
impl<'lt> From<&'lt Generics> for FragmentRef<'lt> {
    fn from(item: &'lt Generics) -> Self {
        Self::Generics(item)
    }
}
impl<'lt> From<&'lt SafetyKind> for FragmentRef<'lt> {
    fn from(item: &'lt SafetyKind) -> Self {
        Self::SafetyKind(item)
    }
}
impl<'lt> From<&'lt Attribute> for FragmentRef<'lt> {
    fn from(item: &'lt Attribute) -> Self {
        Self::Attribute(item)
    }
}
impl<'lt> From<&'lt AttributeKind> for FragmentRef<'lt> {
    fn from(item: &'lt AttributeKind) -> Self {
        Self::AttributeKind(item)
    }
}
impl<'lt> From<&'lt DocCommentKind> for FragmentRef<'lt> {
    fn from(item: &'lt DocCommentKind) -> Self {
        Self::DocCommentKind(item)
    }
}
impl<'lt> From<&'lt SpannedTy> for FragmentRef<'lt> {
    fn from(item: &'lt SpannedTy) -> Self {
        Self::SpannedTy(item)
    }
}
impl<'lt> From<&'lt Param> for FragmentRef<'lt> {
    fn from(item: &'lt Param) -> Self {
        Self::Param(item)
    }
}
impl<'lt> From<&'lt Variant> for FragmentRef<'lt> {
    fn from(item: &'lt Variant) -> Self {
        Self::Variant(item)
    }
}
impl<'lt> From<&'lt ItemKind> for FragmentRef<'lt> {
    fn from(item: &'lt ItemKind) -> Self {
        Self::ItemKind(item)
    }
}
impl<'lt> From<&'lt Item> for FragmentRef<'lt> {
    fn from(item: &'lt Item) -> Self {
        Self::Item(item)
    }
}

/// A borrowed fragment of the AST: this enumeration can represent any node in the AST.
#[derive(Copy)]
#[derive_group_for_ast_base]
#[allow(missing_docs)]
pub enum FragmentRef<'lt> {
    GenericValue(&'lt GenericValue),
    PrimitiveTy(&'lt PrimitiveTy),
    Region(&'lt Region),
    Ty(&'lt Ty),
    DynTraitGoal(&'lt DynTraitGoal),
    Metadata(&'lt Metadata),
    Expr(&'lt Expr),
    Pat(&'lt Pat),
    Arm(&'lt Arm),
    Guard(&'lt Guard),
    BorrowKind(&'lt BorrowKind),
    BindingMode(&'lt BindingMode),
    PatKind(&'lt PatKind),
    GuardKind(&'lt GuardKind),
    Lhs(&'lt Lhs),
    ImplExpr(&'lt ImplExpr),
    ImplExprKind(&'lt ImplExprKind),
    ImplItem(&'lt ImplItem),
    ImplItemKind(&'lt ImplItemKind),
    TraitItem(&'lt TraitItem),
    TraitItemKind(&'lt TraitItemKind),
    QuoteContent(&'lt QuoteContent),
    Quote(&'lt Quote),
    ItemQuoteOrigin(&'lt ItemQuoteOrigin),
    ItemQuoteOriginKind(&'lt ItemQuoteOriginKind),
    ItemQuoteOriginPosition(&'lt ItemQuoteOriginPosition),
    LoopKind(&'lt LoopKind),
    ControlFlowKind(&'lt ControlFlowKind),
    LoopState(&'lt LoopState),
    ExprKind(&'lt ExprKind),
    GenericParamKind(&'lt GenericParamKind),
    TraitGoal(&'lt TraitGoal),
    ImplIdent(&'lt ImplIdent),
    ProjectionPredicate(&'lt ProjectionPredicate),
    GenericConstraint(&'lt GenericConstraint),
    GenericParam(&'lt GenericParam),
    Generics(&'lt Generics),
    SafetyKind(&'lt SafetyKind),
    Attribute(&'lt Attribute),
    AttributeKind(&'lt AttributeKind),
    DocCommentKind(&'lt DocCommentKind),
    SpannedTy(&'lt SpannedTy),
    Param(&'lt Param),
    Variant(&'lt Variant),
    ItemKind(&'lt ItemKind),
    Item(&'lt Item),
}
