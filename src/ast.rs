// Keel abstract syntax tree.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Span {
    pub line: u32,
    pub col: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ty {
    I64,
    Bool,
    Unit,
    /// Owned heap array `[i64]`. Freed when its scope ends unless returned.
    Arr,
    /// Shared borrow `&[i64]`. Lives only for the duration of a call.
    Ref,
    /// Exclusive borrow `&mut [i64]`. Lives only for the duration of a call.
    RefMut,
}

impl Ty {
    pub fn is_array(self) -> bool {
        matches!(self, Ty::Arr | Ty::Ref | Ty::RefMut)
    }
    pub fn name(self) -> &'static str {
        match self {
            Ty::I64 => "i64",
            Ty::Bool => "bool",
            Ty::Unit => "unit",
            Ty::Arr => "[i64]",
            Ty::Ref => "&[i64]",
            Ty::RefMut => "&mut [i64]",
        }
    }
}

#[derive(Clone, Debug)]
pub struct Param {
    pub name: String,
    pub ty: Ty,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Func {
    pub name: String,
    pub io: bool,
    pub params: Vec<Param>,
    pub ret: Ty,
    pub requires: Vec<Expr>,
    pub ensures: Vec<Expr>,
    pub decreases: Option<Expr>,
    pub body: Block,
    pub span: Span,
}

pub type Block = Vec<Stmt>;

#[derive(Clone, Debug)]
pub struct ParBranch {
    pub name: String,
    pub ty: Ty,
    pub call: Expr,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum StmtK {
    Let { name: String, ty: Ty, init: Expr, mutable: bool },
    Assign { name: String, val: Expr },
    Store { name: String, idx: Expr, val: Expr },
    If { cond: Expr, then: Block, els: Option<Block> },
    While { cond: Expr, invs: Vec<Expr>, dec: Expr, body: Block },
    Return(Option<Expr>),
    Assert(Expr),
    Par(Vec<ParBranch>),
    Expr(Expr),
}

#[derive(Clone, Debug)]
pub struct Stmt {
    pub k: StmtK,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UOp {
    Neg,
    Not,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
    Implies,
}

impl BOp {
    pub fn sym(self) -> &'static str {
        match self {
            BOp::Add => "+",
            BOp::Sub => "-",
            BOp::Mul => "*",
            BOp::Div => "/",
            BOp::Mod => "%",
            BOp::Eq => "==",
            BOp::Ne => "!=",
            BOp::Lt => "<",
            BOp::Le => "<=",
            BOp::Gt => ">",
            BOp::Ge => ">=",
            BOp::And => "&&",
            BOp::Or => "||",
            BOp::Implies => "==>",
        }
    }
}

#[derive(Clone, Debug)]
pub enum ExprK {
    Int(i128),
    Bool(bool),
    Var(String),
    Result,
    Call(String, Vec<Expr>),
    Index(String, Box<Expr>),
    Unary(UOp, Box<Expr>),
    Binary(BOp, Box<Expr>, Box<Expr>),
    Quant { forall: bool, var: String, lo: Box<Expr>, hi: Box<Expr>, body: Box<Expr> },
    Borrow { name: String, mutable: bool },
}

#[derive(Clone, Debug)]
pub struct Expr {
    pub k: ExprK,
    pub span: Span,
}
