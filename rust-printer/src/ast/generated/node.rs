impl From<GenericValue> for Node {
    fn from(item: GenericValue) -> Self {
        Self::GenericValue(item)
    }
}
impl From<PrimitiveTy> for Node {
    fn from(item: PrimitiveTy) -> Self {
        Self::PrimitiveTy(item)
    }
}
impl From<Region> for Node {
    fn from(item: Region) -> Self {
        Self::Region(item)
    }
}
impl From<Ty> for Node {
    fn from(item: Ty) -> Self {
        Self::Ty(item)
    }
}
impl From<DynTraitGoal> for Node {
    fn from(item: DynTraitGoal) -> Self {
        Self::DynTraitGoal(item)
    }
}
impl From<Metadata> for Node {
    fn from(item: Metadata) -> Self {
        Self::Metadata(item)
    }
}
impl From<Expr> for Node {
    fn from(item: Expr) -> Self {
        Self::Expr(item)
    }
}
impl From<Pat> for Node {
    fn from(item: Pat) -> Self {
        Self::Pat(item)
    }
}
impl From<Arm> for Node {
    fn from(item: Arm) -> Self {
        Self::Arm(item)
    }
}
impl From<Guard> for Node {
    fn from(item: Guard) -> Self {
        Self::Guard(item)
    }
}
impl From<BorrowKind> for Node {
    fn from(item: BorrowKind) -> Self {
        Self::BorrowKind(item)
    }
}
impl From<BindingMode> for Node {
    fn from(item: BindingMode) -> Self {
        Self::BindingMode(item)
    }
}
impl From<PatKind> for Node {
    fn from(item: PatKind) -> Self {
        Self::PatKind(item)
    }
}
impl From<GuardKind> for Node {
    fn from(item: GuardKind) -> Self {
        Self::GuardKind(item)
    }
}
impl From<Lhs> for Node {
    fn from(item: Lhs) -> Self {
        Self::Lhs(item)
    }
}
impl From<ImplExpr> for Node {
    fn from(item: ImplExpr) -> Self {
        Self::ImplExpr(item)
    }
}
impl From<ImplExprKind> for Node {
    fn from(item: ImplExprKind) -> Self {
        Self::ImplExprKind(item)
    }
}
impl From<ImplItem> for Node {
    fn from(item: ImplItem) -> Self {
        Self::ImplItem(item)
    }
}
impl From<ImplItemKind> for Node {
    fn from(item: ImplItemKind) -> Self {
        Self::ImplItemKind(item)
    }
}
impl From<TraitItem> for Node {
    fn from(item: TraitItem) -> Self {
        Self::TraitItem(item)
    }
}
impl From<TraitItemKind> for Node {
    fn from(item: TraitItemKind) -> Self {
        Self::TraitItemKind(item)
    }
}
impl From<QuoteContent> for Node {
    fn from(item: QuoteContent) -> Self {
        Self::QuoteContent(item)
    }
}
impl From<Quote> for Node {
    fn from(item: Quote) -> Self {
        Self::Quote(item)
    }
}
impl From<ItemQuoteOrigin> for Node {
    fn from(item: ItemQuoteOrigin) -> Self {
        Self::ItemQuoteOrigin(item)
    }
}
impl From<ItemQuoteOriginKind> for Node {
    fn from(item: ItemQuoteOriginKind) -> Self {
        Self::ItemQuoteOriginKind(item)
    }
}
impl From<ItemQuoteOriginPosition> for Node {
    fn from(item: ItemQuoteOriginPosition) -> Self {
        Self::ItemQuoteOriginPosition(item)
    }
}
impl From<LoopKind> for Node {
    fn from(item: LoopKind) -> Self {
        Self::LoopKind(item)
    }
}
impl From<ControlFlowKind> for Node {
    fn from(item: ControlFlowKind) -> Self {
        Self::ControlFlowKind(item)
    }
}
impl From<LoopState> for Node {
    fn from(item: LoopState) -> Self {
        Self::LoopState(item)
    }
}
impl From<ExprKind> for Node {
    fn from(item: ExprKind) -> Self {
        Self::ExprKind(item)
    }
}
impl From<GenericParamKind> for Node {
    fn from(item: GenericParamKind) -> Self {
        Self::GenericParamKind(item)
    }
}
impl From<TraitGoal> for Node {
    fn from(item: TraitGoal) -> Self {
        Self::TraitGoal(item)
    }
}
impl From<ImplIdent> for Node {
    fn from(item: ImplIdent) -> Self {
        Self::ImplIdent(item)
    }
}
impl From<ProjectionPredicate> for Node {
    fn from(item: ProjectionPredicate) -> Self {
        Self::ProjectionPredicate(item)
    }
}
impl From<GenericConstraint> for Node {
    fn from(item: GenericConstraint) -> Self {
        Self::GenericConstraint(item)
    }
}
impl From<GenericParam> for Node {
    fn from(item: GenericParam) -> Self {
        Self::GenericParam(item)
    }
}
impl From<Generics> for Node {
    fn from(item: Generics) -> Self {
        Self::Generics(item)
    }
}
impl From<SafetyKind> for Node {
    fn from(item: SafetyKind) -> Self {
        Self::SafetyKind(item)
    }
}
impl From<Attribute> for Node {
    fn from(item: Attribute) -> Self {
        Self::Attribute(item)
    }
}
impl From<AttributeKind> for Node {
    fn from(item: AttributeKind) -> Self {
        Self::AttributeKind(item)
    }
}
impl From<DocCommentKind> for Node {
    fn from(item: DocCommentKind) -> Self {
        Self::DocCommentKind(item)
    }
}
impl From<SpannedTy> for Node {
    fn from(item: SpannedTy) -> Self {
        Self::SpannedTy(item)
    }
}
impl From<Param> for Node {
    fn from(item: Param) -> Self {
        Self::Param(item)
    }
}
impl From<Variant> for Node {
    fn from(item: Variant) -> Self {
        Self::Variant(item)
    }
}
impl From<ItemKind> for Node {
    fn from(item: ItemKind) -> Self {
        Self::ItemKind(item)
    }
}
impl From<Item> for Node {
    fn from(item: Item) -> Self {
        Self::Item(item)
    }
}
#[derive()]
#[macro_rules_attribute::apply(derive_AST)]
pub enum Node {
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
impl<'lt> From<&'lt GenericValue> for NodeRef<'lt> {
    fn from(item: &'lt GenericValue) -> Self {
        Self::GenericValue(item)
    }
}
impl<'lt> From<&'lt PrimitiveTy> for NodeRef<'lt> {
    fn from(item: &'lt PrimitiveTy) -> Self {
        Self::PrimitiveTy(item)
    }
}
impl<'lt> From<&'lt Region> for NodeRef<'lt> {
    fn from(item: &'lt Region) -> Self {
        Self::Region(item)
    }
}
impl<'lt> From<&'lt Ty> for NodeRef<'lt> {
    fn from(item: &'lt Ty) -> Self {
        Self::Ty(item)
    }
}
impl<'lt> From<&'lt DynTraitGoal> for NodeRef<'lt> {
    fn from(item: &'lt DynTraitGoal) -> Self {
        Self::DynTraitGoal(item)
    }
}
impl<'lt> From<&'lt Metadata> for NodeRef<'lt> {
    fn from(item: &'lt Metadata) -> Self {
        Self::Metadata(item)
    }
}
impl<'lt> From<&'lt Expr> for NodeRef<'lt> {
    fn from(item: &'lt Expr) -> Self {
        Self::Expr(item)
    }
}
impl<'lt> From<&'lt Pat> for NodeRef<'lt> {
    fn from(item: &'lt Pat) -> Self {
        Self::Pat(item)
    }
}
impl<'lt> From<&'lt Arm> for NodeRef<'lt> {
    fn from(item: &'lt Arm) -> Self {
        Self::Arm(item)
    }
}
impl<'lt> From<&'lt Guard> for NodeRef<'lt> {
    fn from(item: &'lt Guard) -> Self {
        Self::Guard(item)
    }
}
impl<'lt> From<&'lt BorrowKind> for NodeRef<'lt> {
    fn from(item: &'lt BorrowKind) -> Self {
        Self::BorrowKind(item)
    }
}
impl<'lt> From<&'lt BindingMode> for NodeRef<'lt> {
    fn from(item: &'lt BindingMode) -> Self {
        Self::BindingMode(item)
    }
}
impl<'lt> From<&'lt PatKind> for NodeRef<'lt> {
    fn from(item: &'lt PatKind) -> Self {
        Self::PatKind(item)
    }
}
impl<'lt> From<&'lt GuardKind> for NodeRef<'lt> {
    fn from(item: &'lt GuardKind) -> Self {
        Self::GuardKind(item)
    }
}
impl<'lt> From<&'lt Lhs> for NodeRef<'lt> {
    fn from(item: &'lt Lhs) -> Self {
        Self::Lhs(item)
    }
}
impl<'lt> From<&'lt ImplExpr> for NodeRef<'lt> {
    fn from(item: &'lt ImplExpr) -> Self {
        Self::ImplExpr(item)
    }
}
impl<'lt> From<&'lt ImplExprKind> for NodeRef<'lt> {
    fn from(item: &'lt ImplExprKind) -> Self {
        Self::ImplExprKind(item)
    }
}
impl<'lt> From<&'lt ImplItem> for NodeRef<'lt> {
    fn from(item: &'lt ImplItem) -> Self {
        Self::ImplItem(item)
    }
}
impl<'lt> From<&'lt ImplItemKind> for NodeRef<'lt> {
    fn from(item: &'lt ImplItemKind) -> Self {
        Self::ImplItemKind(item)
    }
}
impl<'lt> From<&'lt TraitItem> for NodeRef<'lt> {
    fn from(item: &'lt TraitItem) -> Self {
        Self::TraitItem(item)
    }
}
impl<'lt> From<&'lt TraitItemKind> for NodeRef<'lt> {
    fn from(item: &'lt TraitItemKind) -> Self {
        Self::TraitItemKind(item)
    }
}
impl<'lt> From<&'lt QuoteContent> for NodeRef<'lt> {
    fn from(item: &'lt QuoteContent) -> Self {
        Self::QuoteContent(item)
    }
}
impl<'lt> From<&'lt Quote> for NodeRef<'lt> {
    fn from(item: &'lt Quote) -> Self {
        Self::Quote(item)
    }
}
impl<'lt> From<&'lt ItemQuoteOrigin> for NodeRef<'lt> {
    fn from(item: &'lt ItemQuoteOrigin) -> Self {
        Self::ItemQuoteOrigin(item)
    }
}
impl<'lt> From<&'lt ItemQuoteOriginKind> for NodeRef<'lt> {
    fn from(item: &'lt ItemQuoteOriginKind) -> Self {
        Self::ItemQuoteOriginKind(item)
    }
}
impl<'lt> From<&'lt ItemQuoteOriginPosition> for NodeRef<'lt> {
    fn from(item: &'lt ItemQuoteOriginPosition) -> Self {
        Self::ItemQuoteOriginPosition(item)
    }
}
impl<'lt> From<&'lt LoopKind> for NodeRef<'lt> {
    fn from(item: &'lt LoopKind) -> Self {
        Self::LoopKind(item)
    }
}
impl<'lt> From<&'lt ControlFlowKind> for NodeRef<'lt> {
    fn from(item: &'lt ControlFlowKind) -> Self {
        Self::ControlFlowKind(item)
    }
}
impl<'lt> From<&'lt LoopState> for NodeRef<'lt> {
    fn from(item: &'lt LoopState) -> Self {
        Self::LoopState(item)
    }
}
impl<'lt> From<&'lt ExprKind> for NodeRef<'lt> {
    fn from(item: &'lt ExprKind) -> Self {
        Self::ExprKind(item)
    }
}
impl<'lt> From<&'lt GenericParamKind> for NodeRef<'lt> {
    fn from(item: &'lt GenericParamKind) -> Self {
        Self::GenericParamKind(item)
    }
}
impl<'lt> From<&'lt TraitGoal> for NodeRef<'lt> {
    fn from(item: &'lt TraitGoal) -> Self {
        Self::TraitGoal(item)
    }
}
impl<'lt> From<&'lt ImplIdent> for NodeRef<'lt> {
    fn from(item: &'lt ImplIdent) -> Self {
        Self::ImplIdent(item)
    }
}
impl<'lt> From<&'lt ProjectionPredicate> for NodeRef<'lt> {
    fn from(item: &'lt ProjectionPredicate) -> Self {
        Self::ProjectionPredicate(item)
    }
}
impl<'lt> From<&'lt GenericConstraint> for NodeRef<'lt> {
    fn from(item: &'lt GenericConstraint) -> Self {
        Self::GenericConstraint(item)
    }
}
impl<'lt> From<&'lt GenericParam> for NodeRef<'lt> {
    fn from(item: &'lt GenericParam) -> Self {
        Self::GenericParam(item)
    }
}
impl<'lt> From<&'lt Generics> for NodeRef<'lt> {
    fn from(item: &'lt Generics) -> Self {
        Self::Generics(item)
    }
}
impl<'lt> From<&'lt SafetyKind> for NodeRef<'lt> {
    fn from(item: &'lt SafetyKind) -> Self {
        Self::SafetyKind(item)
    }
}
impl<'lt> From<&'lt Attribute> for NodeRef<'lt> {
    fn from(item: &'lt Attribute) -> Self {
        Self::Attribute(item)
    }
}
impl<'lt> From<&'lt AttributeKind> for NodeRef<'lt> {
    fn from(item: &'lt AttributeKind) -> Self {
        Self::AttributeKind(item)
    }
}
impl<'lt> From<&'lt DocCommentKind> for NodeRef<'lt> {
    fn from(item: &'lt DocCommentKind) -> Self {
        Self::DocCommentKind(item)
    }
}
impl<'lt> From<&'lt SpannedTy> for NodeRef<'lt> {
    fn from(item: &'lt SpannedTy) -> Self {
        Self::SpannedTy(item)
    }
}
impl<'lt> From<&'lt Param> for NodeRef<'lt> {
    fn from(item: &'lt Param) -> Self {
        Self::Param(item)
    }
}
impl<'lt> From<&'lt Variant> for NodeRef<'lt> {
    fn from(item: &'lt Variant) -> Self {
        Self::Variant(item)
    }
}
impl<'lt> From<&'lt ItemKind> for NodeRef<'lt> {
    fn from(item: &'lt ItemKind) -> Self {
        Self::ItemKind(item)
    }
}
impl<'lt> From<&'lt Item> for NodeRef<'lt> {
    fn from(item: &'lt Item) -> Self {
        Self::Item(item)
    }
}
#[derive(Copy)]
#[macro_rules_attribute::apply(derive_AST_base)]
pub enum NodeRef<'lt> {
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
