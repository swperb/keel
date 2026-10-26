// Static checks that run before verification: names, types, borrows,
// effects, spec purity, ghost-code rules, exhaustive matches, definite
// return, recursion shape.

use crate::ast::*;
use crate::diag::Diag;
use std::collections::{HashMap, HashSet};

pub struct Sig {
    pub params: Vec<Ty>,
    pub ret: Ty,
    pub io: bool,
    pub kind: FnKind,
}

pub fn sigs(funcs: &[Func]) -> HashMap<String, Sig> {
    let mut m = HashMap::new();
    for f in funcs {
        m.insert(f.name.clone(), Sig { params: f.params.iter().map(|p| p.ty).collect(), ret: f.ret, io: f.io, kind: f.kind });
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
    prog: &'a Program,
    sigs: &'a HashMap<String, Sig>,
    funcs: &'a HashMap<String, &'a Func>,
    f: &'a Func,
    /// True inside a lemma body (ghost code).
    ghost: bool,
    scopes: Vec<HashMap<String, Local>>,
    diags: Vec<Diag>,
    calls: HashSet<String>,
    /// The whole expression of the statement being checked: the only place
    /// a call that takes `&mut` may appear. C leaves the evaluation order of
    /// operands and arguments unspecified, so a mutating call nested inside
    /// a larger expression could run before or after its neighbours read
    /// the same array.
    top: *const Expr,
    /// `old(..)` is meaningful here (ensures, and invariants/asserts in a body).
    old_ok: bool,
}

const BUILTINS: &[&str] = &["len", "array", "print", "count"];

impl<'a> Checker<'a> {
    fn err(&mut self, d: Diag) {
        self.diags.push(d);
    }
    fn lookup(&self, n: &str) -> Option<Local> {
        self.scopes.iter().rev().find_map(|s| s.get(n).copied())
    }
    fn declare(&mut self, n: &str, l: Local, span: Span) {
        if self.lookup(n).is_some() {
            self.err(Diag::new("E-NAME", span, format!("'{}' is already in scope (no shadowing)", n)).hint("pick a new, descriptive name"));
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

    fn want(&mut self, got: Ty, want: Ty, span: Span, what: &str) {
        if got != want {
            self.err(Diag::new("E-TYPE", span, format!("{} must be {}, found {}", what, want.name(), got.name())));
        }
    }

    fn variant_index(&mut self, id: u32, name: &str, span: Span) -> Option<usize> {
        let Some(vs) = self.prog.variants(id) else {
            self.err(Diag::new("E-TYPE", span, format!("'{}' is a struct, not an enum", type_name(id))));
            return None;
        };
        let i = vs.iter().position(|v| v.name == name);
        if i.is_none() {
            let names: Vec<&str> = vs.iter().map(|v| v.name.as_str()).collect();
            self.err(Diag::new("E-NAME", span, format!("enum '{}' has no variant '{}' (variants: {})", type_name(id), name, names.join(", "))));
        }
        i
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
                    UOp::Neg | UOp::BitNot => {
                        self.want(t, Ty::I64, a.span, if *op == UOp::Neg { "operand of '-'" } else { "operand of '~'" });
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
                    BOp::Add | BOp::Sub | BOp::Mul | BOp::Div | BOp::Mod | BOp::BitAnd | BOp::BitOr | BOp::BitXor | BOp::Shl | BOp::Shr => {
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
                            self.err(Diag::new("E-TYPE", e.span, format!("cannot compare {} with {} (only i64 and bool support ==; compare fields or use 'is')", ta.name(), tb.name())));
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
            ExprK::Old(inner) => {
                if ctx == Ctx::Code || !self.old_ok {
                    self.err(Diag::new("E-SPEC", e.span, "old(..) is only allowed in ensures, loop invariants and asserts"));
                }
                self.expr(inner, ctx, false)
            }
            ExprK::Quant { var, range, body, .. } => {
                if ctx == Ctx::Code {
                    self.err(Diag::new("E-SPEC", e.span, "quantifiers are only allowed in specifications"));
                }
                if let Some((lo, hi)) = range {
                    let tl = self.expr(lo, ctx, false);
                    let th = self.expr(hi, ctx, false);
                    self.want(tl, Ty::I64, lo.span, "quantifier bound");
                    self.want(th, Ty::I64, hi.span, "quantifier bound");
                }
                self.scopes.push(HashMap::new());
                self.declare(var, Local { ty: Ty::I64, mutable: false }, e.span);
                let tb = self.expr(body, ctx, false);
                self.want(tb, Ty::Bool, body.span, "quantifier body");
                self.scopes.pop();
                Ty::Bool
            }
            ExprK::IfE(c, a, b) => {
                if ctx == Ctx::Code {
                    self.err(Diag::new("E-SPEC", e.span, "'if' expressions are only allowed in specifications; use an if statement"));
                }
                let tc = self.expr(c, ctx, false);
                self.want(tc, Ty::Bool, c.span, "condition");
                let ta = self.expr(a, ctx, false);
                let tb = self.expr(b, ctx, false);
                self.want(tb, ta, b.span, "else branch");
                ta
            }
            ExprK::Lit { ty, variant, fields } => {
                let want: Vec<Field> = match variant {
                    None => match self.prog.struct_fields(*ty) {
                        Some(f) => f.clone(),
                        None => {
                            self.err(Diag::new("E-TYPE", e.span, format!("'{}' is an enum; write {}.Variant", type_name(*ty), type_name(*ty))));
                            return Ty::Named(*ty);
                        }
                    },
                    Some(v) => match self.variant_index(*ty, v, e.span) {
                        Some(i) => self.prog.variants(*ty).unwrap()[i].fields.clone(),
                        None => return Ty::Named(*ty),
                    },
                };
                let got: Vec<&str> = fields.iter().map(|(n, _)| n.as_str()).collect();
                let exp: Vec<&str> = want.iter().map(|f| f.name.as_str()).collect();
                if got != exp {
                    self.err(Diag::new("E-TYPE", e.span, format!("fields must be given exactly once, in declaration order: {{ {} }}", exp.join(", "))));
                }
                for ((_, fe), fd) in fields.iter().zip(&want) {
                    let t = self.expr(fe, ctx, false);
                    self.want(t, fd.ty, fe.span, &format!("field '{}'", fd.name));
                }
                Ty::Named(*ty)
            }
            ExprK::Field(base, f) => {
                let tb = self.expr(base, ctx, false);
                match self.prog.fields_of(tb).and_then(|fs| fs.iter().find(|x| x.name == *f)) {
                    Some(fd) => fd.ty,
                    None => {
                        self.err(Diag::new("E-TYPE", e.span, format!("{} has no field '{}'", tb.name(), f)));
                        Ty::I64
                    }
                }
            }
            ExprK::Is(base, id, v) => {
                let tb = self.expr(base, ctx, false);
                self.want(tb, Ty::Named(*id), base.span, "left side of 'is'");
                self.variant_index(*id, v, e.span);
                Ty::Bool
            }
            ExprK::As(base, id, v) => {
                if ctx == Ctx::Code {
                    self.err(Diag::new("E-SPEC", e.span, "'as' is only allowed in specifications; use match in code"));
                }
                let tb = self.expr(base, ctx, false);
                self.want(tb, Ty::Named(*id), base.span, "left side of 'as'");
                match self.variant_index(*id, v, e.span) {
                    Some(i) => Ty::Payload(*id, i as u32),
                    None => Ty::I64,
                }
            }
            ExprK::Call(name, args) => {
                if !std::ptr::eq(e, self.top) && args.iter().any(|a| matches!(a.k, ExprK::Borrow { mutable: true, .. })) {
                    self.err(Diag::new("E-BORROW", e.span, format!("a call that takes &mut ('{}') must be a whole statement, initializer, assigned value, return value or condition", name))
                        .hint("bind its result first: let r: i64 = f(&mut xs); then use r"));
                }
                self.call(name, args, e.span, ctx)
            }
        }
    }

    fn call(&mut self, name: &str, args: &[Expr], span: Span, ctx: Ctx) -> Ty {
        if name == "count" {
            // count(&xs, lo, hi, v): occurrences of v in xs[lo..hi]; specifications only.
            if ctx == Ctx::Code {
                self.err(Diag::new("E-SPEC", span, "count(..) is a specification function; use it in contracts, invariants and asserts"));
            }
            if args.len() != 4 {
                self.err(Diag::new("E-TYPE", span, "count takes (&xs, lo, hi, v)"));
                return Ty::I64;
            }
            match &args[0].k {
                ExprK::Borrow { name, mutable: false, range: None } => {
                    self.array_var(name, args[0].span);
                }
                _ => self.err(Diag::new("E-TYPE", args[0].span, "count's first argument is a shared borrow of an array, e.g. &xs")),
            }
            for a in &args[1..] {
                let t = self.expr(a, ctx, false);
                self.want(t, Ty::I64, a.span, "count argument");
            }
            return Ty::I64;
        }
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
        let callee_kind = self.sigs.get(name).map(|s| s.kind);
        // A pure, loop-free fn is lifted to a definition (see lift.rs).
        let lifted = ctx != Ctx::Code && callee_kind == Some(FnKind::Code) && crate::lift::why_not(self.funcs, name).is_none();
        if ctx != Ctx::Code && callee_kind != Some(FnKind::Spec) && !lifted {
            let mut d = Diag::new("E-SPEC", span, format!("specifications may only call spec fns, len, count, and fns that are pure and loop-free, not '{}'", name));
            if callee_kind == Some(FnKind::Code) {
                if let Some(why) = crate::lift::why_not(self.funcs, name) {
                    d = d.hint(format!("{}; write a 'spec fn' for it, and prove they agree with ensures result == spec(..)", why));
                }
            }
            self.err(d);
            return Ty::I64;
        }
        if ctx == Ctx::Code && callee_kind == Some(FnKind::Spec) {
            self.err(Diag::new("E-SPEC", span, format!("'{}' is a spec fn (mathematics, not code) and can only be used in specifications", name)));
            return self.sigs[name].ret;
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
        if sig.kind == FnKind::Lemma {
            self.err(Diag::new("E-SPEC", span, format!("lemma '{}' can only be invoked as a statement", name)));
        }
        if self.ghost && sig.kind == FnKind::Code && !lifted {
            self.err(Diag::new("E-SPEC", span, format!("lemmas may not call executable function '{}'", name)));
        }
        if sig.io && !self.f.io {
            self.err(Diag::new("E-EFFECT", span, format!("'{}' is io; only an 'io fn' may call it", name)));
        }
        self.args(name, args, span, ctx)
    }

    fn args(&mut self, name: &str, args: &[Expr], span: Span, ctx: Ctx) -> Ty {
        let sig = &self.sigs[name];
        if sig.params.len() != args.len() {
            self.err(Diag::new("E-TYPE", span, format!("'{}' takes {} arguments, got {}", name, sig.params.len(), args.len())));
            return sig.ret;
        }
        let params = sig.params.clone();
        let ret = sig.ret;
        for (a, pt) in args.iter().zip(params) {
            if pt.is_array() {
                let ExprK::Borrow { name: an, mutable, range } = &a.k else {
                    self.err(Diag::new("E-BORROW", a.span, format!("expected {} here, write '{}name'", pt.name(), if pt == Ty::RefMut { "&mut " } else { "&" })));
                    continue;
                };
                let Some(l) = self.array_var(an, a.span) else { continue };
                if *mutable != (pt == Ty::RefMut) {
                    self.err(Diag::new("E-BORROW", a.span, format!("parameter expects {}", pt.name())));
                }
                if *mutable && !(l.ty == Ty::Arr || l.ty == Ty::RefMut) {
                    self.err(Diag::new("E-BORROW", a.span, format!("cannot borrow '{}' as &mut: it is {}", an, l.ty.name())));
                }
                if let Some((lo, hi)) = range {
                    for b in [lo, hi] {
                        let t = self.expr(b, ctx, false);
                        self.want(t, Ty::I64, b.span, "slice bound");
                    }
                }
            } else {
                let t = self.expr(a, ctx, false);
                self.want(t, pt, a.span, "argument");
            }
        }
        let items: Vec<(String, bool, bool, usize)> = Self::borrows_of(args).into_iter().enumerate().map(|(i, (n, m, sl))| (n, m, sl, i)).collect();
        self.conflicts(&items, span, "in this call");
        ret
    }

    /// Array uses by call arguments: (name, exclusive, is_slice).
    fn borrows_of(args: &[Expr]) -> Vec<(String, bool, bool)> {
        let mut out = vec![];
        for a in args {
            match &a.k {
                ExprK::Borrow { name, mutable, range } => out.push((name.clone(), *mutable, range.is_some())),
                ExprK::Index(name, _) => out.push((name.clone(), false, false)),
                _ => {}
            }
        }
        out
    }

    /// Two uses of one array conflict when either is exclusive, unless both
    /// are slices; slice pairs are left to the verifier to prove disjoint.
    fn conflicts(&mut self, items: &[(String, bool, bool, usize)], span: Span, place: &str) {
        for i in 0..items.len() {
            for j in i + 1..items.len() {
                let (a, b) = (&items[i], &items[j]);
                if a.0 == b.0 && a.3 != b.3 && (a.1 || b.1) && !(a.2 && b.2) {
                    self.err(Diag::new("E-BORROW", span, format!("'{}' is borrowed &mut and also used elsewhere {} (data race)", a.0, place))
                        .hint("borrow disjoint slices instead, e.g. &mut xs[0..mid] and &mut xs[mid..len(xs)]"));
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

    fn ghost_forbid(&mut self, s: &Stmt, what: &str) -> bool {
        if self.ghost {
            self.err(Diag::new("E-SPEC", s.span, format!("{} is not allowed in a lemma; lemmas prove by cases, asserts and recursion (induction)", what)));
        }
        self.ghost
    }

    /// Expression context for non-spec expressions in the current body.
    fn code(&self) -> Ctx {
        if self.ghost {
            Ctx::Spec
        } else {
            Ctx::Code
        }
    }

    fn stmt(&mut self, s: &Stmt) {
        let cx = self.code();
        self.top = match &s.k {
            StmtK::Let { init: e, .. } | StmtK::Assign { val: e, .. } | StmtK::Return(Some(e)) | StmtK::Expr(e) => e,
            StmtK::If { cond: e, .. } | StmtK::While { cond: e, .. } => e,
            _ => std::ptr::null(),
        };
        match &s.k {
            StmtK::Let { name, ty, init, mutable } => {
                if matches!(ty, Ty::Ref | Ty::RefMut) {
                    self.err(Diag::new("E-TYPE", s.span, "locals cannot hold borrows; borrow at the call site instead"));
                }
                if *ty == Ty::Arr && *mutable {
                    self.err(Diag::new("E-MUT", s.span, "arrays are bound with 'let'; their elements are still writable"));
                }
                if *ty == Ty::Arr && self.ghost_forbid(s, "allocating an array") {
                    return;
                }
                if *ty == Ty::Arr && matches!(init.k, ExprK::Var(_)) {
                    self.err(Diag::new("E-ARRAY", init.span, "arrays cannot be moved between locals; borrow instead"));
                }
                let t = self.expr(init, cx, *ty == Ty::Arr);
                self.want(t, *ty, init.span, &format!("initializer of '{}'", name));
                self.declare(name, Local { ty: *ty, mutable: *mutable }, s.span);
            }
            StmtK::Assign { name, path, val } => {
                let tv = self.expr(val, cx, false);
                match self.lookup(name) {
                    Some(l) if l.mutable => {
                        let mut t = l.ty;
                        for f in path {
                            let fty = self.prog.struct_fields_ty(t, f);
                            match fty {
                                Some(ft) => t = ft,
                                None => {
                                    self.err(Diag::new("E-TYPE", s.span, format!("{} has no assignable field '{}'", t.name(), f)));
                                    return;
                                }
                            }
                        }
                        self.want(tv, t, val.span, &format!("value assigned to '{}'", name));
                    }
                    Some(_) => self.err(Diag::new("E-MUT", s.span, format!("'{}' is not a 'var'", name))),
                    None => self.err(Diag::new("E-NAME", s.span, format!("unknown name '{}'", name))),
                }
            }
            StmtK::Store { name, idx, val } => {
                if self.ghost_forbid(s, "writing an array") {
                    return;
                }
                if let Some(l) = self.array_var(name, s.span) {
                    if l.ty == Ty::Ref {
                        self.err(Diag::new("E-MUT", s.span, format!("'{}' is a shared borrow (&[i64]); writing needs &mut [i64]", name)));
                    }
                }
                let ti = self.expr(idx, cx, false);
                self.want(ti, Ty::I64, idx.span, "array index");
                let tv = self.expr(val, cx, false);
                self.want(tv, Ty::I64, val.span, "stored value");
            }
            StmtK::If { cond, then, els } => {
                let t = self.expr(cond, cx, false);
                self.want(t, Ty::Bool, cond.span, "if condition");
                self.block(then);
                if let Some(e) = els {
                    self.block(e);
                }
            }
            StmtK::Match { scrut, enum_id, arms } => {
                let t = self.expr(scrut, cx, false);
                self.want(t, Ty::Named(*enum_id), scrut.span, "match scrutinee");
                let Some(vs) = self.prog.variants(*enum_id).cloned() else {
                    self.err(Diag::new("E-TYPE", s.span, format!("'{}' is a struct; match works on enums", type_name(*enum_id))));
                    return;
                };
                let got: Vec<&str> = arms.iter().map(|a| a.variant.as_str()).collect();
                let exp: Vec<&str> = vs.iter().map(|v| v.name.as_str()).collect();
                if got != exp {
                    self.err(Diag::new("E-MATCH", s.span, format!("match must list every variant exactly once, in declaration order: {}", exp.join(", "))).hint("there is no wildcard arm; handle each variant explicitly"));
                }
                for a in arms {
                    if a.enum_id != *enum_id {
                        self.err(Diag::new("E-MATCH", a.span, format!("arm names enum '{}' but the scrutinee is '{}'", type_name(a.enum_id), type_name(*enum_id))));
                        continue;
                    }
                    let vi = vs.iter().position(|v| v.name == a.variant);
                    self.scopes.push(HashMap::new());
                    if let Some(vi) = vi {
                        match (&a.binder, vs[vi].fields.is_empty()) {
                            (Some(b), false) => self.declare(b, Local { ty: Ty::Payload(*enum_id, vi as u32), mutable: false }, a.span),
                            (None, true) => {}
                            (Some(_), true) => self.err(Diag::new("E-MATCH", a.span, format!("variant '{}' has no payload; drop the binder", a.variant))),
                            (None, false) => self.err(Diag::new("E-MATCH", a.span, format!("variant '{}' has a payload; bind it: {}.{}(name)", a.variant, type_name(*enum_id), a.variant))),
                        }
                    }
                    self.block(&a.body);
                    self.scopes.pop();
                }
            }
            StmtK::While { cond, invs, dec, body } => {
                if self.ghost_forbid(s, "a loop") {
                    return;
                }
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
                    self.expr(e, cx, false);
                    self.err(Diag::new("E-TYPE", s.span, "this function returns unit"));
                }
                (Some(e), r) => {
                    let t = self.expr(e, cx, r == Ty::Arr);
                    self.want(t, r, e.span, "return value");
                }
            },
            StmtK::Assert(e) => {
                let t = self.expr(e, Ctx::Spec, false);
                self.want(t, Ty::Bool, e.span, "assert condition");
            }
            StmtK::Expr(e) => {
                // A lemma invocation is a ghost statement with spec-context arguments.
                if let ExprK::Call(name, args) = &e.k {
                    if self.sigs.get(name).map(|s| s.kind) == Some(FnKind::Lemma) {
                        self.calls.insert(name.clone());
                        self.args(name, args, e.span, Ctx::Spec);
                        return;
                    }
                }
                if self.ghost {
                    self.err(Diag::new("E-SPEC", s.span, "lemma bodies may only invoke other lemmas"));
                    return;
                }
                if !matches!(e.k, ExprK::Call(..)) {
                    self.err(Diag::new("E-DISCARD", s.span, "expression statements must be calls"));
                }
                let t = self.expr(e, Ctx::Code, false);
                if t != Ty::Unit {
                    self.err(Diag::new("E-DISCARD", s.span, format!("result of type {} is discarded; bind it with 'let'", t.name())));
                }
            }
            StmtK::Par(branches) => {
                if self.ghost_forbid(s, "par") {
                    return;
                }
                let mut items: Vec<(String, bool, bool, usize)> = vec![];
                for (bi, b) in branches.iter().enumerate() {
                    self.top = &b.call;
                    let ExprK::Call(fname, _) = &b.call.k else {
                        self.err(Diag::new("E-PARSE", b.span, "each 'par' branch must be a single function call"));
                        continue;
                    };
                    if matches!(b.ty, Ty::Arr | Ty::Ref | Ty::RefMut) {
                        self.err(Diag::new("E-TYPE", b.span, "par branches return unit, a scalar, a struct or an enum"));
                    }
                    if fname == "print" || self.sigs.get(fname).map(|s| s.io).unwrap_or(false) {
                        self.err(Diag::new("E-EFFECT", b.span, "par branches must be pure (not io)"));
                    }
                    let t = self.expr(&b.call, Ctx::Code, false);
                    self.want(t, b.ty, b.call.span, &format!("par branch '{}'", b.name.as_deref().unwrap_or(fname)));
                    if let ExprK::Call(_, args) = &b.call.k {
                        items.extend(Self::borrows_of(args).into_iter().map(|(n, m, sl)| (n, m, sl, bi)));
                        // Every branch's arguments are evaluated before any
                        // branch runs, so an array read anywhere in them must
                        // not be one another branch writes.
                        let mut rd = vec![];
                        args.iter().for_each(|a| index_reads(a, &mut rd));
                        items.extend(rd.into_iter().map(|n| (n, false, false, bi)));
                    }
                }
                self.conflicts(&items, s.span, "in another par branch");
                for b in branches {
                    if let Some(n) = &b.name {
                        self.declare(n, Local { ty: b.ty, mutable: false }, b.span);
                    }
                }
            }
        }
    }
}

impl Program {
    /// Type of field `f` when assigning through a struct (payloads are immutable).
    pub fn struct_fields_ty(&self, t: Ty, f: &str) -> Option<Ty> {
        match t {
            Ty::Named(id) => self.struct_fields(id)?.iter().find(|x| x.name == f).map(|x| x.ty),
            _ => None,
        }
    }
}

/// Arrays read by indexing anywhere inside `e`.
fn index_reads(e: &Expr, out: &mut Vec<String>) {
    match &e.k {
        ExprK::Index(n, i) => {
            out.push(n.clone());
            index_reads(i, out);
        }
        ExprK::Borrow { range: Some((lo, hi)), .. } => {
            index_reads(lo, out);
            index_reads(hi, out);
        }
        ExprK::Call(_, args) => args.iter().for_each(|a| index_reads(a, out)),
        ExprK::Unary(_, a) | ExprK::Field(a, _) | ExprK::Is(a, _, _) | ExprK::As(a, _, _) => index_reads(a, out),
        ExprK::Binary(_, a, b) => {
            index_reads(a, out);
            index_reads(b, out);
        }
        ExprK::Lit { fields, .. } => fields.iter().for_each(|(_, f)| index_reads(f, out)),
        _ => {}
    }
}

fn always_returns(b: &Block) -> bool {
    match b.last().map(|s| &s.k) {
        Some(StmtK::Return(_)) => true,
        Some(StmtK::If { then, els: Some(e), .. }) => always_returns(then) && always_returns(e),
        Some(StmtK::Match { arms, .. }) => arms.iter().all(|a| always_returns(&a.body)),
        _ => false,
    }
}

fn check_types(prog: &Program, diags: &mut Vec<Diag>) {
    for d in &prog.types {
        if ["Int", "Bool", "Real", "Array", "String"].contains(&d.name.as_str()) {
            diags.push(Diag::new("E-NAME", d.span, format!("'{}' is reserved; pick another type name", d.name)));
        }
        let fields: Vec<&Field> = match &d.kind {
            TypeKind::Struct(f) => f.iter().collect(),
            TypeKind::Enum(vs) => {
                let mut seen = HashSet::new();
                for v in vs {
                    if !seen.insert(&v.name) {
                        diags.push(Diag::new("E-NAME", v.span, format!("duplicate variant '{}'", v.name)));
                    }
                }
                if vs.is_empty() {
                    diags.push(Diag::new("E-TYPE", d.span, "an enum needs at least one variant"));
                }
                vs.iter().flat_map(|v| v.fields.iter()).collect()
            }
        };
        let mut seen = HashSet::new();
        for f in &fields {
            if f.ty.is_array() || f.ty == Ty::Unit {
                diags.push(Diag::new("E-TYPE", f.span, "fields may be i64, bool, or another struct/enum (no arrays yet)"));
            }
            if matches!(d.kind, TypeKind::Struct(_)) && !seen.insert(&f.name) {
                diags.push(Diag::new("E-NAME", f.span, format!("duplicate field '{}'", f.name)));
            }
        }
        // Reject recursive types (they would need heap indirection).
        let mut stack: Vec<u32> = fields.iter().filter_map(|f| if let Ty::Named(i) = f.ty { Some(i) } else { None }).collect();
        let mut seen_ids = HashSet::new();
        while let Some(i) = stack.pop() {
            if i == d.id {
                diags.push(Diag::new("E-TYPE", d.span, format!("'{}' contains itself; recursive types are not supported yet", d.name)));
                break;
            }
            if seen_ids.insert(i) {
                let inner: Vec<&Field> = match &prog.def(i).kind {
                    TypeKind::Struct(f) => f.iter().collect(),
                    TypeKind::Enum(vs) => vs.iter().flat_map(|v| v.fields.iter()).collect(),
                };
                stack.extend(inner.iter().filter_map(|f| if let Ty::Named(j) = f.ty { Some(j) } else { None }));
            }
        }
    }
}

pub fn check(prog: &Program, need_main: bool) -> Vec<Diag> {
    let funcs = &prog.funcs;
    let sigs = sigs(funcs);
    let fmap: HashMap<String, &Func> = funcs.iter().map(|f| (f.name.clone(), f)).collect();
    let mut diags = vec![];
    check_types(prog, &mut diags);
    let mut graph: HashMap<String, HashSet<String>> = HashMap::new();
    let mut names = HashSet::new();
    for f in funcs {
        if !names.insert(f.name.clone()) || BUILTINS.contains(&f.name.as_str()) {
            diags.push(Diag::new("E-NAME", f.span, format!("function '{}' is already defined", f.name)));
        }
        let ghost = f.kind != FnKind::Code;
        let mut c = Checker { prog, sigs: &sigs, funcs: &fmap, f, ghost: f.kind == FnKind::Lemma, scopes: vec![HashMap::new()], diags: vec![], calls: HashSet::new(), top: std::ptr::null(), old_ok: false };
        for p in &f.params {
            if p.ty == Ty::Arr {
                c.err(Diag::new("E-TYPE", p.span, format!("parameter '{}' cannot own an array; take &[i64] or &mut [i64]", p.name)));
            }
            if ghost && matches!(p.ty, Ty::Arr | Ty::RefMut) {
                c.err(Diag::new("E-SPEC", p.span, "spec fns and lemmas take arrays only as &[i64]"));
            }
            c.declare(&p.name, Local { ty: p.ty, mutable: false }, p.span);
        }
        match f.kind {
            FnKind::Lemma if f.ret != Ty::Unit => c.err(Diag::new("E-SPEC", f.span, "lemmas return nothing; state the fact in 'ensures'")),
            FnKind::Spec if !matches!(f.ret, Ty::I64 | Ty::Bool | Ty::Named(_)) => c.err(Diag::new("E-SPEC", f.span, "spec fns return i64, bool, or a struct/enum")),
            FnKind::Spec if !f.ensures.is_empty() => c.err(Diag::new("E-SPEC", f.span, "spec fns are definitions; prove facts about them with a lemma instead of 'ensures'")),
            _ => {}
        }
        for r in &f.requires {
            let t = c.expr(r, Ctx::Spec, false);
            c.want(t, Ty::Bool, r.span, "requires clause");
        }
        if let Some(d) = &f.decreases {
            let t = c.expr(d, Ctx::Spec, false);
            c.want(t, Ty::I64, d.span, "decreases measure");
        }
        if c.calls.contains(&f.name) {
            c.err(Diag::new("E-RECURSION", f.span, format!("'{}' calls itself in its own requires or decreases", f.name)).hint("state the precondition without the function being defined"));
        }
        c.old_ok = f.kind == FnKind::Code;
        for r in &f.ensures {
            let t = c.expr(r, Ctx::Ensures, false);
            c.want(t, Ty::Bool, r.span, "ensures clause");
        }
        c.old_ok = false;
        if f.kind == FnKind::Spec {
            let StmtK::Return(Some(e)) = &f.body[0].k else { unreachable!() };
            let t = c.expr(e, Ctx::Spec, false);
            c.want(t, f.ret, e.span, "spec fn body");
        } else {
            c.old_ok = f.kind == FnKind::Code;
            c.block(&f.body);
        }
        if f.ret != Ty::Unit && !always_returns(&f.body) {
            c.err(Diag::new("E-RETURN", f.span, format!("'{}' may reach the end without returning a {}", f.name, f.ret.name())).hint("end every path with 'return'"));
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
