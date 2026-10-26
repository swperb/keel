// Lexer and recursive-descent parser. The grammar is LL(1) and has no
// operator precedence between unrelated operators (see E-PAREN).

use crate::ast::*;
use crate::diag::Diag;

#[derive(Clone, Debug, PartialEq)]
enum Tok {
    Ident(String),
    Int(i128),
    Kw(&'static str),
    P(&'static str),
    Eof,
}

const KEYWORDS: &[&str] = &[
    "fn", "io", "let", "var", "if", "else", "while", "invariant", "decreases", "requires", "ensures",
    "return", "assert", "par", "forall", "exists", "in", "true", "false", "result", "mut", "i64", "bool",
    "struct", "enum", "match", "is", "as", "spec", "lemma",
];

// Longest first so `==>` wins over `==`.
const PUNCT: &[&str] = &[
    "==>", "=>", "->", "==", "!=", "<=", ">=", "&&", "||", "..", ".", "+", "-", "*", "/", "%", "<", ">", "!", "=",
    "(", ")", "{", "}", "[", "]", ",", ":", ";", "&",
];

fn lex(src: &str) -> Result<Vec<(Tok, Span)>, Diag> {
    let b = src.as_bytes();
    let (mut i, mut line, mut col) = (0usize, 1u32, 1u32);
    let mut out = vec![];
    while i < b.len() {
        let c = b[i];
        if c == b'\n' {
            i += 1;
            line += 1;
            col = 1;
            continue;
        }
        if c.is_ascii_whitespace() {
            i += 1;
            col += 1;
            continue;
        }
        if c == b'/' && i + 1 < b.len() && b[i + 1] == b'/' {
            while i < b.len() && b[i] != b'\n' {
                i += 1;
            }
            continue;
        }
        let span = Span { line, col };
        if c.is_ascii_alphabetic() || c == b'_' {
            let s = i;
            while i < b.len() && (b[i].is_ascii_alphanumeric() || b[i] == b'_') {
                i += 1;
            }
            let w = &src[s..i];
            col += (i - s) as u32;
            let t = match KEYWORDS.iter().find(|k| **k == w) {
                Some(k) => Tok::Kw(k),
                None => Tok::Ident(w.to_string()),
            };
            out.push((t, span));
            continue;
        }
        if c.is_ascii_digit() {
            let s = i;
            while i < b.len() && (b[i].is_ascii_digit() || b[i] == b'_') {
                i += 1;
            }
            col += (i - s) as u32;
            let digits: String = src[s..i].chars().filter(|c| *c != '_').collect();
            match digits.parse::<i128>() {
                Ok(v) if v <= (i64::MAX as i128) + 1 => out.push((Tok::Int(v), span)),
                _ => return Err(Diag::new("E-LEX", span, "integer literal does not fit in i64")),
            }
            continue;
        }
        match PUNCT.iter().find(|p| src[i..].starts_with(**p)) {
            Some(p) => {
                i += p.len();
                col += p.len() as u32;
                out.push((Tok::P(p), span));
            }
            None => {
                return Err(Diag::new("E-LEX", span, format!("unexpected character '{}'", src[i..].chars().next().unwrap())))
            }
        }
    }
    out.push((Tok::Eof, Span { line, col }));
    Ok(out)
}

struct Parser {
    toks: Vec<(Tok, Span)>,
    pos: usize,
    /// Interned type names and where each was first mentioned.
    tnames: Vec<String>,
    tspans: Vec<Span>,
}

fn is_upper(s: &str) -> bool {
    s.chars().next().map(|c| c.is_ascii_uppercase()).unwrap_or(false)
}

type PResult<T> = Result<T, Diag>;

fn desc(t: &Tok) -> String {
    match t {
        Tok::Ident(s) => format!("identifier '{}'", s),
        Tok::Int(v) => format!("integer {}", v),
        Tok::Kw(k) => format!("keyword '{}'", k),
        Tok::P(p) => format!("'{}'", p),
        Tok::Eof => "end of file".into(),
    }
}

impl Parser {
    fn peek(&self) -> &Tok {
        &self.toks[self.pos].0
    }
    fn span(&self) -> Span {
        self.toks[self.pos].1
    }
    fn bump(&mut self) -> Tok {
        let t = self.toks[self.pos].0.clone();
        if self.pos + 1 < self.toks.len() {
            self.pos += 1;
        }
        t
    }
    fn is_p(&self, p: &str) -> bool {
        matches!(self.peek(), Tok::P(q) if *q == p)
    }
    fn is_kw(&self, k: &str) -> bool {
        matches!(self.peek(), Tok::Kw(q) if *q == k)
    }
    fn err<T>(&self, what: &str) -> PResult<T> {
        Err(Diag::new("E-PARSE", self.span(), format!("expected {}, found {}", what, desc(self.peek()))))
    }
    fn expect_p(&mut self, p: &str) -> PResult<()> {
        if self.is_p(p) {
            self.bump();
            Ok(())
        } else {
            self.err(&format!("'{}'", p))
        }
    }
    fn expect_kw(&mut self, k: &str) -> PResult<()> {
        if self.is_kw(k) {
            self.bump();
            Ok(())
        } else {
            self.err(&format!("'{}'", k))
        }
    }
    /// A value name (variable, function, field): must start lowercase.
    fn ident(&mut self) -> PResult<String> {
        match self.peek().clone() {
            Tok::Ident(s) if !is_upper(&s) => {
                self.bump();
                Ok(s)
            }
            Tok::Ident(s) => Err(Diag::new("E-NAME", self.span(), format!("'{}': value names start with a lowercase letter; uppercase is reserved for types", s))),
            _ => self.err("identifier"),
        }
    }

    /// A type or variant name: must start uppercase.
    fn upper(&mut self) -> PResult<String> {
        match self.peek().clone() {
            Tok::Ident(s) if is_upper(&s) => {
                self.bump();
                Ok(s)
            }
            Tok::Ident(s) => Err(Diag::new("E-NAME", self.span(), format!("'{}': type and variant names start with an uppercase letter", s))),
            _ => self.err("type name"),
        }
    }

    fn intern(&mut self, name: &str, span: Span) -> u32 {
        if let Some(i) = self.tnames.iter().position(|n| n == name) {
            return i as u32;
        }
        self.tnames.push(name.to_string());
        self.tspans.push(span);
        (self.tnames.len() - 1) as u32
    }

    fn fields(&mut self) -> PResult<Vec<Field>> {
        self.expect_p("{")?;
        let mut v = vec![];
        while !self.is_p("}") {
            let span = self.span();
            let name = self.ident()?;
            self.expect_p(":")?;
            let ty = self.ty()?;
            v.push(Field { name, ty, span });
            if !self.is_p("}") {
                self.expect_p(",")?;
            }
        }
        self.bump();
        Ok(v)
    }

    fn typedef(&mut self) -> PResult<TypeDef> {
        let span = self.span();
        let is_struct = self.is_kw("struct");
        self.bump();
        let name = self.upper()?;
        let id = self.intern(&name, span);
        let kind = if is_struct {
            TypeKind::Struct(self.fields()?)
        } else {
            self.expect_p("{")?;
            let mut vs = vec![];
            while !self.is_p("}") {
                let vspan = self.span();
                let vname = self.upper()?;
                let fields = if self.is_p("{") { self.fields()? } else { vec![] };
                vs.push(Variant { name: vname, fields, span: vspan });
                if !self.is_p("}") {
                    self.expect_p(",")?;
                }
            }
            self.bump();
            TypeKind::Enum(vs)
        };
        Ok(TypeDef { id, name, kind, span })
    }

    fn ty(&mut self) -> PResult<Ty> {
        if self.is_kw("i64") {
            self.bump();
            return Ok(Ty::I64);
        }
        if self.is_kw("bool") {
            self.bump();
            return Ok(Ty::Bool);
        }
        if let Tok::Ident(n) = self.peek().clone() {
            if is_upper(&n) {
                let span = self.span();
                self.bump();
                return Ok(Ty::Named(self.intern(&n, span)));
            }
        }
        let mut t = Ty::Arr;
        if self.is_p("&") {
            self.bump();
            t = Ty::Ref;
            if self.is_kw("mut") {
                self.bump();
                t = Ty::RefMut;
            }
        }
        if !self.is_p("[") {
            return self.err("a type (i64, bool, [i64], &[i64], &mut [i64], or a struct/enum name)");
        }
        self.bump();
        self.expect_kw("i64")?;
        self.expect_p("]")?;
        Ok(t)
    }

    fn func(&mut self) -> PResult<Func> {
        let span = self.span();
        let mut io = false;
        let mut kind = FnKind::Code;
        if self.is_kw("io") {
            self.bump();
            io = true;
            self.expect_kw("fn")?;
        } else if self.is_kw("spec") {
            self.bump();
            kind = FnKind::Spec;
            self.expect_kw("fn")?;
        } else if self.is_kw("lemma") {
            self.bump();
            kind = FnKind::Lemma;
        } else {
            self.expect_kw("fn")?;
        }
        let name = self.ident()?;
        self.expect_p("(")?;
        let mut params = vec![];
        while !self.is_p(")") {
            let ps = self.span();
            let pname = self.ident()?;
            self.expect_p(":")?;
            let ty = self.ty()?;
            params.push(Param { name: pname, ty, span: ps });
            if !self.is_p(")") {
                self.expect_p(",")?;
            }
        }
        self.bump();
        let ret = if self.is_p("->") {
            self.bump();
            self.ty()?
        } else {
            Ty::Unit
        };
        let (mut requires, mut ensures, mut decreases) = (vec![], vec![], None);
        loop {
            if self.is_kw("requires") {
                self.bump();
                requires.push(self.expr()?);
            } else if self.is_kw("ensures") {
                self.bump();
                ensures.push(self.expr()?);
            } else if self.is_kw("decreases") {
                if decreases.is_some() {
                    return self.err("at most one 'decreases' clause");
                }
                self.bump();
                decreases = Some(self.expr()?);
            } else {
                break;
            }
        }
        let body = if kind == FnKind::Spec {
            // A spec fn body is a single expression.
            self.expect_p("{")?;
            let bspan = self.span();
            let e = self.expr()?;
            self.expect_p("}")?;
            vec![Stmt { k: StmtK::Return(Some(e)), span: bspan }]
        } else {
            self.block()?
        };
        Ok(Func { name, kind, io, params, ret, requires, ensures, decreases, body, span })
    }

    fn block(&mut self) -> PResult<Block> {
        self.expect_p("{")?;
        let mut v = vec![];
        while !self.is_p("}") {
            if *self.peek() == Tok::Eof {
                return self.err("'}'");
            }
            v.push(self.stmt()?);
        }
        self.bump();
        Ok(v)
    }

    fn stmt(&mut self) -> PResult<Stmt> {
        let span = self.span();
        let k = match self.peek().clone() {
            Tok::Kw("let") | Tok::Kw("var") => {
                let mutable = self.is_kw("var");
                self.bump();
                let name = self.ident()?;
                self.expect_p(":")?;
                let ty = self.ty()?;
                self.expect_p("=")?;
                let init = self.expr()?;
                self.expect_p(";")?;
                StmtK::Let { name, ty, init, mutable }
            }
            Tok::Kw("if") => return self.if_stmt(),
            Tok::Kw("while") => {
                self.bump();
                let cond = self.expr()?;
                let mut invs = vec![];
                while self.is_kw("invariant") {
                    self.bump();
                    invs.push(self.expr()?);
                }
                if !self.is_kw("decreases") {
                    return self.err("'invariant' or 'decreases' (every loop must state a termination measure)");
                }
                self.bump();
                let dec = self.expr()?;
                let body = self.block()?;
                StmtK::While { cond, invs, dec, body }
            }
            Tok::Kw("return") => {
                self.bump();
                let e = if self.is_p(";") { None } else { Some(self.expr()?) };
                self.expect_p(";")?;
                StmtK::Return(e)
            }
            Tok::Kw("assert") => {
                self.bump();
                let e = self.expr()?;
                self.expect_p(";")?;
                StmtK::Assert(e)
            }
            Tok::Kw("par") => {
                self.bump();
                self.expect_p("{")?;
                let mut branches = vec![];
                while !self.is_p("}") {
                    let bs = self.span();
                    let (name, ty) = if self.is_kw("let") {
                        self.bump();
                        let name = self.ident()?;
                        self.expect_p(":")?;
                        let ty = self.ty()?;
                        self.expect_p("=")?;
                        (Some(name), ty)
                    } else {
                        (None, Ty::Unit)
                    };
                    let call = self.expr()?;
                    self.expect_p(";")?;
                    branches.push(ParBranch { name, ty, call, span: bs });
                }
                self.bump();
                if branches.len() < 2 {
                    return Err(Diag::new("E-PARSE", span, "a 'par' block needs at least two branches"));
                }
                StmtK::Par(branches)
            }
            Tok::Ident(name) if matches!(self.toks[self.pos + 1].0, Tok::P("=") | Tok::P(".")) => {
                self.bump();
                let mut path = vec![];
                while self.is_p(".") {
                    self.bump();
                    path.push(self.ident()?);
                }
                self.expect_p("=")?;
                let val = self.expr()?;
                self.expect_p(";")?;
                StmtK::Assign { name, path, val }
            }
            Tok::Kw("match") => {
                self.bump();
                let scrut = self.expr()?;
                self.expect_p("{")?;
                let mut arms = vec![];
                let mut enum_id = None;
                while !self.is_p("}") {
                    let aspan = self.span();
                    let tname = self.upper()?;
                    let id = self.intern(&tname, aspan);
                    if enum_id.is_none() {
                        enum_id = Some(id);
                    }
                    self.expect_p(".")?;
                    let variant = self.upper()?;
                    let binder = if self.is_p("(") {
                        self.bump();
                        let b = self.ident()?;
                        self.expect_p(")")?;
                        Some(b)
                    } else {
                        None
                    };
                    self.expect_p("=>")?;
                    let body = self.block()?;
                    arms.push(Arm { enum_id: id, variant, binder, body, span: aspan });
                }
                self.bump();
                let Some(enum_id) = enum_id else {
                    return Err(Diag::new("E-PARSE", span, "a match needs at least one arm"));
                };
                StmtK::Match { scrut, enum_id, arms }
            }
            Tok::Ident(name) if matches!(self.toks[self.pos + 1].0, Tok::P("[")) => {
                // Either `xs[i] = v;` or an expression statement starting with an index.
                let save = self.pos;
                self.bump();
                self.bump();
                let idx = self.expr()?;
                self.expect_p("]")?;
                if self.is_p("=") {
                    self.bump();
                    let val = self.expr()?;
                    self.expect_p(";")?;
                    StmtK::Store { name, idx, val }
                } else {
                    self.pos = save;
                    let e = self.expr()?;
                    self.expect_p(";")?;
                    StmtK::Expr(e)
                }
            }
            _ => {
                let e = self.expr()?;
                self.expect_p(";")?;
                StmtK::Expr(e)
            }
        };
        Ok(Stmt { k, span })
    }

    fn if_stmt(&mut self) -> PResult<Stmt> {
        let span = self.span();
        self.expect_kw("if")?;
        let cond = self.expr()?;
        let then = self.block()?;
        let els = if self.is_kw("else") {
            self.bump();
            if self.is_kw("if") {
                Some(vec![self.if_stmt()?])
            } else {
                Some(self.block()?)
            }
        } else {
            None
        };
        Ok(Stmt { k: StmtK::If { cond, then, els }, span })
    }

    // expr := logic ["==>" logic]
    fn expr(&mut self) -> PResult<Expr> {
        let lhs = self.logic()?;
        if self.is_p("==>") {
            let span = self.span();
            self.bump();
            let rhs = self.logic()?;
            if self.is_p("==>") {
                return Err(Diag::new("E-PAREN", self.span(), "'==>' does not chain; add parentheses"));
            }
            return Ok(Expr { k: ExprK::Binary(BOp::Implies, Box::new(lhs), Box::new(rhs)), span });
        }
        Ok(lhs)
    }

    // logic := cmp ("&&" cmp)* | cmp ("||" cmp)*   (no mixing)
    fn logic(&mut self) -> PResult<Expr> {
        let mut lhs = self.cmp()?;
        let mut first: Option<BOp> = None;
        loop {
            let op = if self.is_p("&&") {
                BOp::And
            } else if self.is_p("||") {
                BOp::Or
            } else {
                break;
            };
            if let Some(f) = first {
                if f != op {
                    return Err(Diag::new("E-PAREN", self.span(), "cannot mix '&&' and '||' without parentheses"));
                }
            }
            first = Some(op);
            let span = self.span();
            self.bump();
            let rhs = self.cmp()?;
            lhs = Expr { k: ExprK::Binary(op, Box::new(lhs), Box::new(rhs)), span };
        }
        Ok(lhs)
    }

    // cmp := arith [cmpop arith]   (non-associative)
    fn cmp(&mut self) -> PResult<Expr> {
        let lhs = self.arith()?;
        if self.is_kw("is") || self.is_kw("as") {
            let is = self.is_kw("is");
            let span = self.span();
            self.bump();
            let tname = self.upper()?;
            let id = self.intern(&tname, span);
            self.expect_p(".")?;
            let variant = self.upper()?;
            let k = if is { ExprK::Is(Box::new(lhs), id, variant) } else { ExprK::As(Box::new(lhs), id, variant) };
            return Ok(Expr { k, span });
        }
        let op = match self.peek() {
            Tok::P("==") => BOp::Eq,
            Tok::P("!=") => BOp::Ne,
            Tok::P("<") => BOp::Lt,
            Tok::P("<=") => BOp::Le,
            Tok::P(">") => BOp::Gt,
            Tok::P(">=") => BOp::Ge,
            _ => return Ok(lhs),
        };
        let span = self.span();
        self.bump();
        let rhs = self.arith()?;
        if matches!(self.peek(), Tok::P("==" | "!=" | "<" | "<=" | ">" | ">=")) {
            return Err(Diag::new("E-PAREN", self.span(), "comparisons do not chain; write 'a <= b && b < c'"));
        }
        Ok(Expr { k: ExprK::Binary(op, Box::new(lhs), Box::new(rhs)), span })
    }

    // arith := unary (op unary)* where all ops belong to one class:
    // {+,-} chains, {*} chains, {/} and {%} take exactly two operands.
    fn arith(&mut self) -> PResult<Expr> {
        let mut lhs = self.unary()?;
        let mut class: Option<u8> = None;
        loop {
            let (op, c) = match self.peek() {
                Tok::P("+") => (BOp::Add, 0),
                Tok::P("-") => (BOp::Sub, 0),
                Tok::P("*") => (BOp::Mul, 1),
                Tok::P("/") => (BOp::Div, 2),
                Tok::P("%") => (BOp::Mod, 3),
                _ => break,
            };
            if let Some(prev) = class {
                if prev != c || c >= 2 {
                    return Err(Diag::new(
                        "E-PAREN",
                        self.span(),
                        format!("'{}' cannot follow a different or non-associative operator without parentheses", op.sym()),
                    ));
                }
            }
            class = Some(c);
            let span = self.span();
            self.bump();
            let rhs = self.unary()?;
            lhs = Expr { k: ExprK::Binary(op, Box::new(lhs), Box::new(rhs)), span };
        }
        Ok(lhs)
    }

    fn unary(&mut self) -> PResult<Expr> {
        let span = self.span();
        if self.is_p("-") {
            self.bump();
            if let Tok::Int(v) = *self.peek() {
                self.bump();
                return Ok(Expr { k: ExprK::Int(-v), span });
            }
            let e = self.unary()?;
            return Ok(Expr { k: ExprK::Unary(UOp::Neg, Box::new(e)), span });
        }
        if self.is_p("!") {
            self.bump();
            let e = self.unary()?;
            return Ok(Expr { k: ExprK::Unary(UOp::Not, Box::new(e)), span });
        }
        let mut e = self.primary()?;
        while self.is_p(".") {
            let span = self.span();
            self.bump();
            let f = self.ident()?;
            e = Expr { k: ExprK::Field(Box::new(e), f), span };
        }
        Ok(e)
    }

    fn primary(&mut self) -> PResult<Expr> {
        let span = self.span();
        let k = match self.bump() {
            Tok::Int(v) => {
                if v > i64::MAX as i128 {
                    return Err(Diag::new("E-LEX", span, "integer literal does not fit in i64"));
                }
                ExprK::Int(v)
            }
            Tok::Kw("true") => ExprK::Bool(true),
            Tok::Kw("false") => ExprK::Bool(false),
            Tok::Kw("result") => ExprK::Result,
            Tok::Kw("if") => {
                let c = self.expr()?;
                self.expect_p("{")?;
                let a = self.expr()?;
                self.expect_p("}")?;
                self.expect_kw("else")?;
                self.expect_p("{")?;
                let b = self.expr()?;
                self.expect_p("}")?;
                ExprK::IfE(Box::new(c), Box::new(a), Box::new(b))
            }
            Tok::P("(") => {
                let e = self.expr()?;
                self.expect_p(")")?;
                return Ok(e);
            }
            Tok::P("&") => {
                let mutable = if self.is_kw("mut") {
                    self.bump();
                    true
                } else {
                    false
                };
                let name = self.ident()?;
                let range = if self.is_p("[") {
                    self.bump();
                    let lo = self.arith()?;
                    self.expect_p("..")?;
                    let hi = self.arith()?;
                    self.expect_p("]")?;
                    Some((Box::new(lo), Box::new(hi)))
                } else {
                    None
                };
                ExprK::Borrow { name, mutable, range }
            }
            Tok::Kw(q @ ("forall" | "exists")) => {
                let var = self.ident()?;
                self.expect_kw("in")?;
                let lo = self.arith()?;
                self.expect_p("..")?;
                let hi = self.arith()?;
                self.expect_p("{")?;
                let body = self.expr()?;
                self.expect_p("}")?;
                ExprK::Quant { forall: q == "forall", var, lo: Box::new(lo), hi: Box::new(hi), body: Box::new(body) }
            }
            Tok::Ident(tname) if is_upper(&tname) => {
                let id = self.intern(&tname, span);
                let variant = if self.is_p(".") {
                    self.bump();
                    Some(self.upper()?)
                } else {
                    None
                };
                let mut fields = vec![];
                // A variant literal takes braces only if they open a field list
                // (`{ name: ...`), so `if s == Shape.Empty { ... }` stays a block.
                let field_list = self.is_p("{")
                    && matches!(self.toks.get(self.pos + 1).map(|t| &t.0), Some(Tok::Ident(_)))
                    && matches!(self.toks.get(self.pos + 2).map(|t| &t.0), Some(Tok::P(":")));
                if field_list || variant.is_none() {
                    self.expect_p("{")?;
                    while !self.is_p("}") {
                        let f = self.ident()?;
                        self.expect_p(":")?;
                        let e = self.expr()?;
                        fields.push((f, e));
                        if !self.is_p("}") {
                            self.expect_p(",")?;
                        }
                    }
                    self.bump();
                }
                ExprK::Lit { ty: id, variant, fields }
            }
            Tok::Ident(name) => {
                if self.is_p("(") {
                    self.bump();
                    let mut args = vec![];
                    while !self.is_p(")") {
                        args.push(self.expr()?);
                        if !self.is_p(")") {
                            self.expect_p(",")?;
                        }
                    }
                    self.bump();
                    ExprK::Call(name, args)
                } else if self.is_p("[") {
                    self.bump();
                    let idx = self.expr()?;
                    self.expect_p("]")?;
                    ExprK::Index(name, Box::new(idx))
                } else {
                    ExprK::Var(name)
                }
            }
            t => {
                return Err(Diag::new("E-PARSE", span, format!("expected an expression, found {}", desc(&t))));
            }
        };
        Ok(Expr { k, span })
    }
}

pub fn parse(src: &str) -> Result<Program, Diag> {
    let toks = lex(src)?;
    let mut p = Parser { toks, pos: 0, tnames: vec![], tspans: vec![] };
    let mut funcs = vec![];
    let mut defs: Vec<TypeDef> = vec![];
    while *p.peek() != Tok::Eof {
        if p.is_kw("struct") || p.is_kw("enum") {
            let d = p.typedef()?;
            if defs.iter().any(|x| x.id == d.id) {
                return Err(Diag::new("E-NAME", d.span, format!("type '{}' is already defined", d.name)));
            }
            defs.push(d);
        } else {
            funcs.push(p.func()?);
        }
    }
    let mut types = vec![];
    for (i, name) in p.tnames.iter().enumerate() {
        match defs.iter().position(|d| d.id == i as u32) {
            Some(j) => types.push(defs[j].clone()),
            None => return Err(Diag::new("E-NAME", p.tspans[i], format!("unknown type '{}'", name))),
        }
    }
    let _ = TYPE_NAMES.set(p.tnames.clone());
    Ok(Program { types, funcs })
}
