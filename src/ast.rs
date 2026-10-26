// Keel abstract syntax tree.

use std::sync::OnceLock;

/// Names of user types, indexed by `Ty::Named` id. Set once after parsing.
pub static TYPE_NAMES: OnceLock<Vec<String>> = OnceLock::new();

pub fn type_name(id: u32) -> String {
    TYPE_NAMES.get().map(|v| v[id as usize].clone()).unwrap_or_else(|| format!("T{}", id))
}

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
    /// A user struct or enum, by id into the program's type table.
    Named(u32),
    /// The payload of an enum variant, bound by a match arm: (enum id, variant index).
    Payload(u32, u32),
}

impl Ty {
    pub fn is_array(self) -> bool {
        matches!(self, Ty::Arr | Ty::Ref | Ty::RefMut)
    }
    pub fn name(self) -> String {
        match self {
            Ty::I64 => "i64".into(),
            Ty::Bool => "bool".into(),
            Ty::Unit => "unit".into(),
            Ty::Arr => "[i64]".into(),
            Ty::Ref => "&[i64]".into(),
            Ty::RefMut => "&mut [i64]".into(),
            Ty::Named(id) => type_name(id),
            Ty::Payload(id, v) => format!("payload of {} variant {}", type_name(id), v),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Field {
    pub name: String,
    pub ty: Ty,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Variant {
    pub name: String,
    /// Empty for a variant without payload.
    pub fields: Vec<Field>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum TypeKind {
    Struct(Vec<Field>),
    Enum(Vec<Variant>),
}

#[derive(Clone, Debug)]
pub struct TypeDef {
    pub id: u32,
    pub name: String,
    pub kind: TypeKind,
    pub span: Span,
}

pub struct Program {
    /// Indexed by type id.
    pub types: Vec<TypeDef>,
    pub funcs: Vec<Func>,
}

impl Program {
    pub fn def(&self, id: u32) -> &TypeDef {
        &self.types[id as usize]
    }
    pub fn struct_fields(&self, id: u32) -> Option<&Vec<Field>> {
        match &self.def(id).kind {
            TypeKind::Struct(f) => Some(f),
            _ => None,
        }
    }
    pub fn variants(&self, id: u32) -> Option<&Vec<Variant>> {
        match &self.def(id).kind {
            TypeKind::Enum(v) => Some(v),
            _ => None,
        }
    }
    /// Fields reachable through `.` on a value of this type.
    pub fn fields_of(&self, t: Ty) -> Option<&Vec<Field>> {
        match t {
            Ty::Named(id) => self.struct_fields(id),
            Ty::Payload(id, v) => self.variants(id).map(|vs| &vs[v as usize].fields),
            _ => None,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Param {
    pub name: String,
    pub ty: Ty,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FnKind {
    /// Executable code (`fn` or `io fn`).
    Code,
    /// `spec fn`: a pure mathematical definition, usable only in specifications.
    Spec,
    /// `lemma`: a ghost proof. Its body is checked, then erased.
    Lemma,
}

#[derive(Clone, Debug)]
pub struct Func {
    pub name: String,
    pub kind: FnKind,
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
    /// None for a unit call branch (`f(..);`).
    pub name: Option<String>,
    pub ty: Ty,
    pub call: Expr,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum StmtK {
    Let { name: String, ty: Ty, init: Expr, mutable: bool },
    /// `name.f.g = val;` (path empty for plain assignment).
    Assign { name: String, path: Vec<String>, val: Expr },
    Store { name: String, idx: Expr, val: Expr },
    If { cond: Expr, then: Block, els: Option<Block> },
    While { cond: Expr, invs: Vec<Expr>, dec: Expr, body: Block },
    Return(Option<Expr>),
    Assert(Expr),
    Par(Vec<ParBranch>),
    Match { scrut: Expr, enum_id: u32, arms: Vec<Arm> },
    Expr(Expr),
}

#[derive(Clone, Debug)]
pub struct Arm {
    pub enum_id: u32,
    pub variant: String,
    pub binder: Option<String>,
    pub body: Block,
    pub span: Span,
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
    /// `forall k in lo..hi { P }`, or with no range `forall v: i64 { P }` (every i64).
    Quant { forall: bool, var: String, range: Option<(Box<Expr>, Box<Expr>)>, body: Box<Expr> },
    /// `old(e)`: `e` evaluated in the state on function entry; specifications only.
    Old(Box<Expr>),
    /// `&xs`, `&mut xs`, or a slice `&xs[lo..hi]` / `&mut xs[lo..hi]`.
    Borrow { name: String, mutable: bool, range: Option<(Box<Expr>, Box<Expr>)> },
    /// `Point { x: 1, y: 2 }` or `Shape.Circle { r: 5 }` or `Shape.Empty`.
    Lit { ty: u32, variant: Option<String>, fields: Vec<(String, Expr)> },
    Field(Box<Expr>, String),
    Is(Box<Expr>, u32, String),
    /// `if c { a } else { b }` as an expression; specifications only.
    IfE(Box<Expr>, Box<Expr>, Box<Expr>),
    /// `(s as Shape.Circle)`: view an enum value as one variant's payload; specifications only.
    As(Box<Expr>, u32, String),
}

#[derive(Clone, Debug)]
pub struct Expr {
    pub k: ExprK,
    pub span: Span,
}
