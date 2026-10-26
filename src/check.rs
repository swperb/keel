// Static checks that run before verification: names, types, borrows,
// effects, spec purity, definite return, recursion shape.

use crate::ast::*;
use crate::diag::Diag;
use std::collections::{HashMap, HashSet};

pub struct Sig {
    pub params: Vec<Ty>,
    pub ret: Ty,
    pub io: bool,
}

pub fn sigs(funcs: &[Func]) -> HashMap<String, Sig> {
    let mut m = HashMap::new();
    for f in funcs {
        m.insert(f.name.clone(), Sig { params: f.params.iter().map(|p| p.ty).collect(), ret: f.ret, io: f.io });
    }
    m
}

#[derive(Clone, Copy)]
struct Local {
    ty: Ty,
    mutable: bool,
}

#[derive(Clone, Copy, PartialEq)]
enum Ctx {
    Code,
    Spec,
    Ensures,
}

struct Checker<'a> {
    sigs: &'a HashMap<String, Sig>,
    f: &'a Func,
    scopes: Vec<HashMap<String, Local>>,
    diags: Vec<Diag>,
    calls: HashSet<String>,
}

const BUILTINS: &[&str] = &["len", "array", "print"];

impl<'a> Checker<'a> {
    fn err(&mut self, d: Diag) {
        self.diags.push(d);
    }
    fn lookup(&self, n: &str) -> Option<Local> {
        self.scopes.iter().rev().find_map(|s| s.get(n).copied())
    }
    fn declare(&mut self, n: &str, l: Local, span: Span) {
        if self.lookup(n).is_some() {
            self.err(Diag::new("E-NAME", span, format!("'{}' is already in scope (no shadowing)", n))
                .hint("pick a new, descriptive name"));
        }
        self.scopes.last_mut().unwrap().insert(n.to_string(), l);
    }

    fn array_var(&mut self, name: &str, span: Span) -> Option<Local> {
        match self.lookup(name) {
            Some(l) if l.ty.is_array() => Some(l),
            Some(l) => {
                self.err(Diag::new("E-TYPE", span, format!("'{}' has type {}, expected an array", name, l.ty.name())));
                None
            }
            None => {
                self.err(Diag::new("E-NAME", span, format!("unknown name '{}'", name)));
                None
            }
        }
    }

    /// Type of an expression. `arr_ok` is true only for `let` initializers
    /// and `return` values, the two places array values may appear.
    fn expr(&mut self, e: &Expr, ctx: Ctx, arr_ok: bool) -> Ty {
        let t = self.expr_inner(e, ctx, arr_ok);
        if t == Ty::Arr && !arr_ok && !matches!(e.k, ExprK::Var(_)) {
            self.err(Diag::new("E-ARRAY", e.span, "array values may only be a 'let' initializer or a 'return' value"));
        }
        t
    }

    fn expr_inner(&mut self, e: &Expr, ctx: Ctx, arr_ok: bool) -> Ty {
        match &e.k {
            ExprK::Int(_) => Ty::I64,
            ExprK::Bool(_) => Ty::Bool,
            ExprK::Result => {
                if ctx != Ctx::Ensures {
                    self.err(Diag::new("E-SPEC", e.span, "'result' is only valid in 'ensures'"));
                    return Ty::I64;
                }
                if self.f.ret == Ty::Unit {
                    self.err(Diag::new("E-SPEC", e.span, "'result' used in a function that returns unit"));
                }
                self.f.ret
            }
            ExprK::Var(n) => match self.lookup(n) {
                Some(l) => {
                    if l.ty.is_array() && !(arr_ok && l.ty == Ty::Arr) {
                        self.err(Diag::new("E-BORROW", e.span, format!("array '{}' must be used as &{} or &mut {}, indexed, or measured with len()", n, n, n)));
                    }
                    l.ty
                }
                None => {
                    self.err(Diag::new("E-NAME", e.span, format!("unknown name '{}'", n)));
                    Ty::I64
                }
            },
            ExprK::Index(n, idx) => {
                self.array_var(n, e.span);
                let it = self.expr(idx, ctx, false);
                self.want(it, Ty::I64, idx.span, "array index");
                Ty::I64
            }
            ExprK::Borrow { .. } => {
                self.err(Diag::new("E-BORROW", e.span, "borrows (&xs, &mut xs) may only appear as call arguments"));
                Ty::Ref
            }
            ExprK::Unary(op, a) => {
                let t = self.expr(a, ctx, false);
                match op {
                    UOp::Neg => {
                        self.want(t, Ty::I64, a.span, "operand of '-'");
                        Ty::I64
                    }
                    UOp::Not => {
                        self.want(t, Ty::Bool, a.span, "operand of '!'");
                        Ty::Bool
                    }
                }
            }
            ExprK::Binary(op, a, b) => {
                let ta = self.expr(a, ctx, false);
                let tb = self.expr(b, ctx, false);
                match op {
                    BOp::Add | BOp::Sub | BOp::Mul | BOp::Div | BOp::Mod => {
                        self.want(ta, Ty::I64, a.span, "arithmetic operand");
                        self.want(tb, Ty::I64, b.span, "arithmetic operand");
                        Ty::I64
                    }
                    BOp::Lt | BOp::Le | BOp::Gt | BOp::Ge => {
                        self.want(ta, Ty::I64, a.span, "comparison operand");
                        self.want(tb, Ty::I64, b.span, "comparison operand");
                        Ty::Bool
                    }
                    BOp::Eq | BOp::Ne => {
                        if ta != tb || !(ta == Ty::I64 || ta == Ty::Bool) {
                            self.err(Diag::new("E-TYPE", e.span, format!("cannot compare {} with {}", ta.name(), tb.name())));
                        }
                        Ty::Bool
                    }
                    BOp::And | BOp::Or | BOp::Implies => {
                        self.want(ta, Ty::Bool, a.span, "logical operand");
                        self.want(tb, Ty::Bool, b.span, "logical operand");
                        Ty::Bool
                    }
                }
            }
            ExprK::Quant { var, lo, hi, body, .. } => {
                if ctx == Ctx::Code {
                    self.err(Diag::new("E-SPEC", e.span, "quantifiers are only allowed in specifications"));
                }
                let tl = self.expr(lo, ctx, false);
                let th = self.expr(hi, ctx, false);
                self.want(tl, Ty::I64, lo.span, "quantifier bound");
                self.want(th, Ty::I64, hi.span, "quantifier bound");
                self.scopes.push(HashMap::new());
                self.declare(var, Local { ty: Ty::I64, mutable: false }, e.span);
                let tb = self.expr(body, ctx, false);
                self.want(tb, Ty::Bool, body.span, "quantifier body");
                self.scopes.pop();
                Ty::Bool
            }
            ExprK::Call(name, args) => self.call(name, args, e.span, ctx, arr_ok),
        }
    }

    fn want(&mut self, got: Ty, want: Ty, span: Span, what: &str) {
        if got != want {
            self.err(Diag::new("E-TYPE", span, format!("{} must be {}, found {}", what, want.name(), got.name())));
        }
    }

    fn call(&mut self, name: &str, args: &[Expr], span: Span, ctx: Ctx, _arr_ok: bool) -> Ty {
        if name == "len" {
            if args.len() != 1 {
                self.err(Diag::new("E-TYPE", span, "len takes exactly one array"));
                return Ty::I64;
            }
            match &args[0].k {
                ExprK::Var(n) => {
                    self.array_var(n, args[0].span);
                }
                ExprK::Result if ctx == Ctx::Ensures && self.f.ret == Ty::Arr => {}
                _ => self.err(Diag::new("E-TYPE", args[0].span, "len takes an array name, e.g. len(xs)")),
            }
            return Ty::I64;
        }
        if ctx != Ctx::Code {
            self.err(Diag::new("E-SPEC", span, format!("specifications may not call '{}' (only len is allowed)", name)));
            return Ty::I64;
        }
        if name == "array" {
            if args.len() != 2 {
                self.err(Diag::new("E-TYPE", span, "array takes (length: i64, fill: i64)"));
                return Ty::Arr;
            }
            for a in args {
                let t = self.expr(a, ctx, false);
                self.want(t, Ty::I64, a.span, "array argument");
            }
            return Ty::Arr;
        }
        if name == "print" {
            if !self.f.io {
                self.err(Diag::new("E-EFFECT", span, "print is io; mark this function 'io fn'"));
            }
            if args.len() != 1 {
                self.err(Diag::new("E-TYPE", span, "print takes exactly one i64"));
                return Ty::Unit;
            }
            let t = self.expr(&args[0], ctx, false);
            self.want(t, Ty::I64, args[0].span, "print argument");
            return Ty::Unit;
        }
        let Some(sig) = self.sigs.get(name) else {
            self.err(Diag::new("E-NAME", span, format!("unknown function '{}'", name)));
            return Ty::I64;
        };
        self.calls.insert(name.to_string());
        if sig.io && !self.f.io {
            self.err(Diag::new("E-EFFECT", span, format!("'{}' is io; only an 'io fn' may call it", name)));
        }
        if sig.params.len() != args.len() {
            self.err(Diag::new("E-TYPE", span, format!("'{}' takes {} arguments, got {}", name, sig.params.len(), args.len())));
            return sig.ret;
        }
        let params = sig.params.clone();
        let ret = sig.ret;
        let mut shared: Vec<String> = vec![];
        let mut excl: Vec<String> = vec![];
        for (a, pt) in args.iter().zip(params) {
            if pt.is_array() {
                let ExprK::Borrow { name: an, mutable } = &a.k else {
                    let hint = if pt == Ty::RefMut { "&mut" } else { "&" };
                    self.err(Diag::new("E-BORROW", a.span, format!("expected {} here, write '{}name'", pt.name(), if hint == "&" { "&" } else { "&mut " })));
                    continue;
                };
                let Some(l) = self.array_var(an, a.span) else { continue };
                if *mutable != (pt == Ty::RefMut) {
                    self.err(Diag::new("E-BORROW", a.span, format!("parameter expects {}", pt.name())));
                }
                if *mutable {
                    if !(l.ty == Ty::Arr || l.ty == Ty::RefMut) {
                        self.err(Diag::new("E-BORROW", a.span, format!("cannot borrow '{}' as &mut: it is {}", an, l.ty.name())));
                    }
                    excl.push(an.clone());
                } else {
                    shared.push(an.clone());
                }
            } else {
                let t = self.expr(a, ctx, false);
                self.want(t, pt, a.span, "argument");
            }
        }
        for (i, x) in excl.iter().enumerate() {
            if shared.contains(x) || excl[i + 1..].contains(x) {
                self.err(Diag::new("E-BORROW", span, format!("'{}' is borrowed &mut while also borrowed elsewhere in this call", x)));
            }
        }
        ret
    }

    fn borrows_of(e: &Expr, out_s: &mut Vec<String>, out_m: &mut Vec<String>) {
        if let ExprK::Call(_, args) = &e.k {
            for a in args {
                match &a.k {
                    ExprK::Borrow { name, mutable: true } => out_m.push(name.clone()),
                    ExprK::Borrow { name, mutable: false } => out_s.push(name.clone()),
                    ExprK::Index(name, _) => out_s.push(name.clone()),
                    _ => {}
                }
            }
        }
    }

    fn block(&mut self, b: &Block) {
        self.scopes.push(HashMap::new());
        for (i, s) in b.iter().enumerate() {
            if i > 0 && matches!(b[i - 1].k, StmtK::Return(_)) {
                self.err(Diag::new("E-UNREACHABLE", s.span, "statement after 'return' is unreachable"));
            }
            self.stmt(s);
        }
        self.scopes.pop();
    }

    fn stmt(&mut self, s: &Stmt) {
        match &s.k {
            StmtK::Let { name, ty, init, mutable } => {
                if matches!(ty, Ty::Ref | Ty::RefMut) {
                    self.err(Diag::new("E-TYPE", s.span, "locals cannot hold borrows; borrow at the call site instead"));
                }
                if *ty == Ty::Arr && *mutable {
                    self.err(Diag::new("E-MUT", s.span, "arrays are bound with 'let'; their elements are still writable"));
                }
                if *ty == Ty::Arr && matches!(init.k, ExprK::Var(_)) {
                    self.err(Diag::new("E-ARRAY", init.span, "arrays cannot be moved between locals; borrow instead"));
                }
                let t = self.expr(init, Ctx::Code, *ty == Ty::Arr);
                self.want(t, *ty, init.span, &format!("initializer of '{}'", name));
                self.declare(name, Local { ty: *ty, mutable: *mutable }, s.span);
            }
            StmtK::Assign { name, val } => {
                let t = self.expr(val, Ctx::Code, false);
                match self.lookup(name) {
                    Some(l) if l.mutable => self.want(t, l.ty, val.span, &format!("value assigned to '{}'", name)),
                    Some(_) => self.err(Diag::new("E-MUT", s.span, format!("'{}' is not a 'var'", name))),
                    None => self.err(Diag::new("E-NAME", s.span, format!("unknown name '{}'", name))),
                }
            }
            StmtK::Store { name, idx, val } => {
                if let Some(l) = self.array_var(name, s.span) {
                    if l.ty == Ty::Ref {
                        self.err(Diag::new("E-MUT", s.span, format!("'{}' is a shared borrow (&[i64]); writing needs &mut [i64]", name)));
                    }
                }
                let ti = self.expr(idx, Ctx::Code, false);
                self.want(ti, Ty::I64, idx.span, "array index");
                let tv = self.expr(val, Ctx::Code, false);
                self.want(tv, Ty::I64, val.span, "stored value");
            }
            StmtK::If { cond, then, els } => {
                let t = self.expr(cond, Ctx::Code, false);
                self.want(t, Ty::Bool, cond.span, "if condition");
                self.block(then);
                if let Some(e) = els {
                    self.block(e);
                }
            }
            StmtK::While { cond, invs, dec, body } => {
                let t = self.expr(cond, Ctx::Code, false);
                self.want(t, Ty::Bool, cond.span, "while condition");
                for i in invs {
                    let t = self.expr(i, Ctx::Spec, false);
                    self.want(t, Ty::Bool, i.span, "invariant");
                }
                let t = self.expr(dec, Ctx::Spec, false);
                self.want(t, Ty::I64, dec.span, "decreases measure");
                self.block(body);
            }
            StmtK::Return(e) => match (e, self.f.ret) {
                (None, Ty::Unit) => {}
                (None, r) => self.err(Diag::new("E-TYPE", s.span, format!("missing return value of type {}", r.name()))),
                (Some(e), Ty::Unit) => {
                    self.expr(e, Ctx::Code, false);
                    self.err(Diag::new("E-TYPE", s.span, "this function returns unit"));
                }
                (Some(e), r) => {
                    let t = self.expr(e, Ctx::Code, r == Ty::Arr);
                    self.want(t, r, e.span, "return value");
                }
            },
            StmtK::Assert(e) => {
                let t = self.expr(e, Ctx::Spec, false);
                self.want(t, Ty::Bool, e.span, "assert condition");
            }
            StmtK::Expr(e) => {
                if !matches!(e.k, ExprK::Call(..)) {
                    self.err(Diag::new("E-DISCARD", s.span, "expression statements must be calls"));
                }
                let t = self.expr(e, Ctx::Code, false);
                if t != Ty::Unit {
                    self.err(Diag::new("E-DISCARD", s.span, format!("result of type {} is discarded; bind it with 'let'", t.name())));
                }
            }
            StmtK::Par(branches) => {
                let mut sets = vec![];
                for b in branches {
                    let ExprK::Call(fname, _) = &b.call.k else {
                        self.err(Diag::new("E-PARSE", b.span, "each 'par' branch must be a single function call"));
                        continue;
                    };
                    if !matches!(b.ty, Ty::I64 | Ty::Bool) {
                        self.err(Diag::new("E-TYPE", b.span, "par branches return i64 or bool in v0"));
                    }
                    if fname == "print" || self.sigs.get(fname).map(|s| s.io).unwrap_or(false) {
                        self.err(Diag::new("E-EFFECT", b.span, "par branches must be pure (not io)"));
                    }
                    let t = self.expr(&b.call, Ctx::Code, false);
                    self.want(t, b.ty, b.call.span, &format!("par branch '{}'", b.name));
                    let (mut sh, mut mu) = (vec![], vec![]);
                    Self::borrows_of(&b.call, &mut sh, &mut mu);
                    sets.push((sh, mu));
                }
                for (i, (_, mu)) in sets.iter().enumerate() {
                    for (j, (sh2, mu2)) in sets.iter().enumerate() {
                        if i != j {
                            for x in mu {
                                if sh2.contains(x) || mu2.contains(x) {
                                    self.err(Diag::new("E-BORROW", s.span, format!("'{}' is borrowed &mut in one par branch and used in another (data race)", x)));
                                }
                            }
                        }
                    }
                }
                for b in branches {
                    self.declare(&b.name, Local { ty: b.ty, mutable: false }, b.span);
                }
            }
        }
    }
}

fn always_returns(b: &Block) -> bool {
    match b.last().map(|s| &s.k) {
        Some(StmtK::Return(_)) => true,
        Some(StmtK::If { then, els: Some(e), .. }) => always_returns(then) && always_returns(e),
        _ => false,
    }
}

pub fn check(funcs: &[Func], need_main: bool) -> Vec<Diag> {
    let sigs = sigs(funcs);
    let mut diags = vec![];
    let mut graph: HashMap<String, HashSet<String>> = HashMap::new();
    let mut names = HashSet::new();
    for f in funcs {
        if !names.insert(f.name.clone()) || BUILTINS.contains(&f.name.as_str()) {
            diags.push(Diag::new("E-NAME", f.span, format!("function '{}' is already defined", f.name)));
        }
        let mut c = Checker { sigs: &sigs, f, scopes: vec![HashMap::new()], diags: vec![], calls: HashSet::new() };
        for p in &f.params {
            c.declare(&p.name, Local { ty: p.ty, mutable: false }, p.span);
        }
        for r in &f.requires {
            let t = c.expr(r, Ctx::Spec, false);
            c.want(t, Ty::Bool, r.span, "requires clause");
        }
        for r in &f.ensures {
            let t = c.expr(r, Ctx::Ensures, false);
            c.want(t, Ty::Bool, r.span, "ensures clause");
        }
        if let Some(d) = &f.decreases {
            let t = c.expr(d, Ctx::Spec, false);
            c.want(t, Ty::I64, d.span, "decreases measure");
        }
        c.block(&f.body);
        if f.ret != Ty::Unit && !always_returns(&f.body) {
            c.err(Diag::new("E-RETURN", f.span, format!("'{}' may reach the end without returning a {}", f.name, f.ret.name()))
                .hint("end every path with 'return'"));
        }
        if c.calls.contains(&f.name) && f.decreases.is_none() {
            c.err(Diag::new("E-RECURSION", f.span, format!("'{}' is recursive and needs a 'decreases' clause", f.name)));
        }
        graph.insert(f.name.clone(), c.calls.clone());
        diags.extend(c.diags);
    }
    // Reject recursion cycles longer than one function.
    for f in funcs {
        let mut stack: Vec<String> = graph[&f.name].iter().filter(|n| **n != f.name).cloned().collect();
        let mut seen = HashSet::new();
        while let Some(n) = stack.pop() {
            if n == f.name {
                diags.push(Diag::new("E-RECURSION", f.span, format!("'{}' is mutually recursive; v0 supports direct recursion only", f.name)));
                break;
            }
            if seen.insert(n.clone()) {
                if let Some(next) = graph.get(&n) {
                    stack.extend(next.iter().cloned());
                }
            }
        }
    }
    if need_main {
        match funcs.iter().find(|f| f.name == "main") {
            Some(m) if m.io && m.params.is_empty() && m.ret == Ty::Unit => {}
            Some(m) => diags.push(Diag::new("E-MAIN", m.span, "main must be declared 'io fn main()' with no parameters or return type")),
            None => diags.push(Diag::new("E-MAIN", Span { line: 1, col: 1 }, "no 'io fn main()' defined")),
        }
    }
    diags
}
