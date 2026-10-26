// Verification-condition generator. Each function is symbolically executed;
// every operation that could misbehave at runtime (overflow, out-of-bounds,
// division by zero, contract violation, non-termination) becomes a proof
// obligation discharged by Z3. Anything not proven is a compile error, which
// is what lets codegen emit zero runtime checks.

use crate::ast::*;
use crate::diag::Diag;
use std::collections::{HashMap, HashSet};
use std::io::Write;
use std::process::{Command, Stdio};

const I64_MIN: i128 = i64::MIN as i128;
const I64_MAX: i128 = i64::MAX as i128;
const MAX_LEN: i128 = 1 << 40;

fn lit(v: i128) -> String {
    if v < 0 {
        format!("(- {})", -v)
    } else {
        v.to_string()
    }
}

fn in_range(t: &str) -> String {
    format!("(and (<= {} {}) (<= {} {}))", lit(I64_MIN), t, t, lit(I64_MAX))
}

#[derive(Clone)]
struct V {
    ty: Ty,
    smt: String,
    len: Option<String>,
}

#[derive(Clone, Default)]
struct St {
    vars: HashMap<String, V>,
    pc: Vec<String>,
    done: bool,
}

struct Obl {
    code: &'static str,
    msg: String,
    hint: &'static str,
    span: Span,
    pc: Vec<String>,
    goal: String,
    cex: Vec<(String, String)>,
}

enum Out {
    Scalar(String),
    Arr(V),
    Unit,
}

struct Gen<'a> {
    funcs: &'a HashMap<String, &'a Func>,
    f: &'a Func,
    decls: Vec<String>,
    obls: Vec<Obl>,
    n: usize,
    dec_entry: Option<String>,
}

impl<'a> Gen<'a> {
    fn fresh(&mut self, base: &str, ty: Ty, st: &mut St) -> String {
        self.n += 1;
        let name = format!("v.{}.{}", base, self.n);
        let sort = match ty {
            Ty::Bool => "Bool",
            t if t.is_array() => "(Array Int Int)",
            _ => "Int",
        };
        self.decls.push(format!("(declare-const {} {})", name, sort));
        if ty == Ty::I64 {
            st.pc.push(in_range(&name));
        }
        name
    }

    fn fresh_len(&mut self, base: &str, st: &mut St) -> String {
        self.n += 1;
        let name = format!("len.{}.{}", base, self.n);
        self.decls.push(format!("(declare-const {} Int)", name));
        st.pc.push(format!("(and (<= 0 {}) (<= {} {}))", name, name, MAX_LEN));
        name
    }

    fn obl(&mut self, st: &St, code: &'static str, span: Span, goal: String, msg: String, hint: &'static str) {
        let mut cex: Vec<(String, String)> = vec![];
        for (k, v) in &st.vars {
            match v.ty {
                Ty::I64 | Ty::Bool => cex.push((k.clone(), v.smt.clone())),
                _ => {
                    if let Some(l) = &v.len {
                        cex.push((format!("len({})", k), l.clone()));
                    }
                }
            }
        }
        cex.sort();
        self.obls.push(Obl { code, msg, hint, span, pc: st.pc.clone(), goal, cex });
    }

    /// Evaluate `e` assuming `cond` (short-circuit semantics). Facts learned
    /// while evaluating `e` are kept, guarded by `cond`.
    fn ex_under(&mut self, st: &mut St, cond: &str, e: &Expr, spec: bool) -> String {
        let base = st.pc.len();
        st.pc.push(cond.to_string());
        let r = self.ex(st, e, spec);
        let extra: Vec<String> = st.pc.drain(base + 1..).collect();
        st.pc.pop();
        if !extra.is_empty() {
            st.pc.push(format!("(=> {} (and true {}))", cond, extra.join(" ")));
        }
        r
    }

    fn ex(&mut self, st: &mut St, e: &Expr, spec: bool) -> String {
        match &e.k {
            ExprK::Int(v) => lit(*v),
            ExprK::Bool(b) => b.to_string(),
            ExprK::Var(n) => st.vars[n].smt.clone(),
            ExprK::Result => st.vars["result"].smt.clone(),
            ExprK::Borrow { .. } => unreachable!("checked"),
            ExprK::Index(n, i) => {
                let iv = self.ex(st, i, spec);
                let a = st.vars[n].clone();
                let len = a.len.clone().unwrap();
                if !spec {
                    self.obl(
                        st,
                        "V-BOUNDS",
                        e.span,
                        format!("(and (<= 0 {}) (< {} {}))", iv, iv, len),
                        format!("index into '{}' may be out of bounds", n),
                        "prove 0 <= index < len(array) with a requires clause or loop invariant",
                    );
                }
                let t = format!("(select {} {})", a.smt, iv);
                if !spec {
                    st.pc.push(in_range(&t));
                }
                t
            }
            ExprK::Unary(UOp::Not, a) => format!("(not {})", self.ex(st, a, spec)),
            ExprK::Unary(UOp::Neg, a) => {
                let t = format!("(- {})", self.ex(st, a, spec));
                if !spec {
                    self.obl(st, "V-OVERFLOW", e.span, in_range(&t), "negation may overflow i64".into(), "bound the operand away from i64::MIN");
                }
                t
            }
            ExprK::Binary(op, a, b) => {
                let av = self.ex(st, a, spec);
                let bv = match op {
                    BOp::And | BOp::Implies => self.ex_under(st, &av, b, spec),
                    BOp::Or => self.ex_under(st, &format!("(not {})", av), b, spec),
                    _ => self.ex(st, b, spec),
                };
                let arith = |s: &str| format!("({} {} {})", s, av, bv);
                match op {
                    BOp::Add | BOp::Sub | BOp::Mul => {
                        let t = arith(match op {
                            BOp::Add => "+",
                            BOp::Sub => "-",
                            _ => "*",
                        });
                        if !spec {
                            self.obl(
                                st,
                                "V-OVERFLOW",
                                e.span,
                                in_range(&t),
                                format!("'{}' may overflow i64", op.sym()),
                                "bound the operands with requires clauses or loop invariants",
                            );
                        }
                        t
                    }
                    BOp::Div | BOp::Mod => {
                        let q = format!("(cdiv {} {})", av, bv);
                        if !spec {
                            self.obl(st, "V-DIVZERO", e.span, format!("(not (= {} 0))", bv), format!("divisor of '{}' may be zero", op.sym()), "prove the divisor is nonzero");
                            st.pc.push(format!("(not (= {} 0))", bv));
                            self.obl(st, "V-OVERFLOW", e.span, in_range(&q), "i64::MIN / -1 overflows".into(), "rule out a divisor of -1 or a dividend of i64::MIN");
                        }
                        if *op == BOp::Div {
                            q
                        } else {
                            format!("(cmod {} {})", av, bv)
                        }
                    }
                    BOp::Eq => arith("="),
                    BOp::Ne => format!("(not {})", arith("=")),
                    BOp::Lt => arith("<"),
                    BOp::Le => arith("<="),
                    BOp::Gt => arith(">"),
                    BOp::Ge => arith(">="),
                    BOp::And => arith("and"),
                    BOp::Or => arith("or"),
                    BOp::Implies => arith("=>"),
                }
            }
            ExprK::Quant { forall, var, lo, hi, body } => {
                let lv = self.ex(st, lo, true);
                let hv = self.ex(st, hi, true);
                self.n += 1;
                let q = format!("q.{}.{}", var, self.n);
                st.vars.insert(var.clone(), V { ty: Ty::I64, smt: q.clone(), len: None });
                let bv = self.ex(st, body, true);
                st.vars.remove(var);
                let range = format!("(and (<= {} {}) (< {} {}))", lv, q, q, hv);
                if *forall {
                    format!("(forall (({} Int)) (=> {} {}))", q, range, bv)
                } else {
                    format!("(exists (({} Int)) (and {} {}))", q, range, bv)
                }
            }
            ExprK::Call(name, args) => match self.call(st, name, args, e.span, spec) {
                Out::Scalar(s) => s,
                Out::Unit => "true".into(),
                Out::Arr(_) => unreachable!("checked"),
            },
        }
    }

    fn ex_arr(&mut self, st: &mut St, e: &Expr) -> V {
        match &e.k {
            ExprK::Var(n) => st.vars[n].clone(),
            ExprK::Call(name, args) => match self.call(st, name, args, e.span, false) {
                Out::Arr(v) => v,
                _ => unreachable!("checked"),
            },
            _ => unreachable!("checked"),
        }
    }

    fn call(&mut self, st: &mut St, name: &str, args: &[Expr], span: Span, spec: bool) -> Out {
        match name {
            "len" => {
                let key = match &args[0].k {
                    ExprK::Var(n) => n.as_str(),
                    _ => "result",
                };
                return Out::Scalar(st.vars[key].len.clone().unwrap());
            }
            "print" => {
                self.ex(st, &args[0], spec);
                return Out::Unit;
            }
            "array" => {
                let nv = self.ex(st, &args[0], spec);
                let fill = self.ex(st, &args[1], spec);
                self.obl(
                    st,
                    "V-ALLOC",
                    span,
                    format!("(and (<= 0 {}) (<= {} {}))", nv, nv, MAX_LEN),
                    "array length may be negative or larger than 2^40".into(),
                    "bound the length with a requires clause",
                );
                let a = self.fresh("arr", Ty::Arr, st);
                let len = self.fresh_len("arr", st);
                st.pc.push(format!("(= {} ((as const (Array Int Int)) {}))", a, fill));
                st.pc.push(format!("(= {} {})", len, nv));
                return Out::Arr(V { ty: Ty::Arr, smt: a, len: Some(len) });
            }
            _ => {}
        }
        let g = self.funcs[name];
        let mut cs = St::default();
        let mut mut_args: Vec<(String, String)> = vec![]; // (caller name, callee param)
        for (a, p) in args.iter().zip(&g.params) {
            if p.ty.is_array() {
                let ExprK::Borrow { name: an, .. } = &a.k else { unreachable!() };
                let v = st.vars[an].clone();
                cs.vars.insert(p.name.clone(), V { ty: p.ty, smt: v.smt, len: v.len });
                if p.ty == Ty::RefMut {
                    mut_args.push((an.clone(), p.name.clone()));
                }
            } else {
                let s = self.ex(st, a, spec);
                cs.vars.insert(p.name.clone(), V { ty: p.ty, smt: s, len: None });
            }
        }
        for r in &g.requires {
            let goal = self.ex(&mut cs, r, true);
            self.obl(st, "V-REQUIRES", span, goal, format!("call to '{}' may violate its precondition", name), "establish the callee's requires clause before the call");
        }
        if g.name == self.f.name {
            let d = self.ex(&mut cs, g.decreases.as_ref().unwrap(), true);
            let entry = self.dec_entry.clone().unwrap();
            self.obl(
                st,
                "V-TERMINATION",
                span,
                format!("(and (<= 0 {}) (< {} {}))", d, d, entry),
                format!("recursive call to '{}' may not decrease the measure", name),
                "the decreases expression must be >= 0 and strictly smaller at every recursive call",
            );
        }
        for (an, pn) in mut_args {
            let a2 = self.fresh(&an, Ty::Arr, st);
            st.vars.get_mut(&an).unwrap().smt = a2.clone();
            cs.vars.get_mut(&pn).unwrap().smt = a2;
        }
        let out = match g.ret {
            Ty::Unit => Out::Unit,
            Ty::Arr => {
                let a = self.fresh("ret", Ty::Arr, st);
                let len = self.fresh_len("ret", st);
                let v = V { ty: Ty::Arr, smt: a, len: Some(len) };
                cs.vars.insert("result".into(), v.clone());
                Out::Arr(v)
            }
            t => {
                let r = self.fresh(&format!("{}.ret", name), t, st);
                cs.vars.insert("result".into(), V { ty: t, smt: r.clone(), len: None });
                Out::Scalar(r)
            }
        };
        for en in &g.ensures {
            let fact = self.ex(&mut cs, en, true);
            st.pc.push(fact);
        }
        out
    }

    fn check_post(&mut self, st: &mut St, result: Option<V>, span: Span) {
        if let Some(r) = result {
            st.vars.insert("result".into(), r);
        }
        let f = self.f;
        for en in &f.ensures {
            let goal = self.ex(st, en, true);
            self.obl(st, "V-ENSURES", span, goal, format!("'{}' may violate its ensures clause on this path", f.name), "strengthen the code, the requires clause, or the loop invariants");
        }
        st.vars.remove("result");
    }

    fn block(&mut self, st: &mut St, b: &Block) {
        for s in b {
            if st.done {
                return;
            }
            self.stmt(st, s);
        }
    }

    fn stmt(&mut self, st: &mut St, s: &Stmt) {
        match &s.k {
            StmtK::Let { name, ty, init, .. } => {
                if *ty == Ty::Arr {
                    let v = self.ex_arr(st, init);
                    st.vars.insert(name.clone(), v);
                } else {
                    let val = self.ex(st, init, false);
                    let x = self.fresh(name, *ty, st);
                    st.pc.push(format!("(= {} {})", x, val));
                    st.vars.insert(name.clone(), V { ty: *ty, smt: x, len: None });
                }
            }
            StmtK::Assign { name, val } => {
                let v = self.ex(st, val, false);
                let ty = st.vars[name].ty;
                let x = self.fresh(name, ty, st);
                st.pc.push(format!("(= {} {})", x, v));
                st.vars.get_mut(name).unwrap().smt = x;
            }
            StmtK::Store { name, idx, val } => {
                let iv = self.ex(st, idx, false);
                let a = st.vars[name].clone();
                self.obl(
                    st,
                    "V-BOUNDS",
                    s.span,
                    format!("(and (<= 0 {}) (< {} {}))", iv, iv, a.len.clone().unwrap()),
                    format!("write to '{}' may be out of bounds", name),
                    "prove 0 <= index < len(array) with a requires clause or loop invariant",
                );
                let vv = self.ex(st, val, false);
                let a2 = self.fresh(name, Ty::Arr, st);
                st.pc.push(format!("(= {} (store {} {} {}))", a2, a.smt, iv, vv));
                st.vars.get_mut(name).unwrap().smt = a2;
            }
            StmtK::If { cond, then, els } => {
                let c = self.ex(st, cond, false);
                let mut t = st.clone();
                t.pc.push(c.clone());
                self.block(&mut t, then);
                let mut e = st.clone();
                e.pc.push(format!("(not {})", c));
                if let Some(eb) = els {
                    self.block(&mut e, eb);
                }
                self.merge(st, &c, t, e);
            }
            StmtK::While { cond, invs, dec, body } => {
                for i in invs {
                    let g = self.ex(st, i, true);
                    self.obl(st, "V-INVARIANT-ENTRY", i.span, g, "loop invariant may not hold on entry".into(), "initialize variables so the invariant holds before the first iteration");
                }
                let mut mods = HashSet::new();
                mods_block(body, &mut mods);
                let mut names: Vec<String> = mods.into_iter().filter(|m| st.vars.contains_key(m)).collect();
                names.sort();
                for m in names {
                    let ty = st.vars[&m].ty;
                    let x = self.fresh(&m, if ty.is_array() { Ty::Arr } else { ty }, st);
                    st.vars.get_mut(&m).unwrap().smt = x;
                }
                for i in invs {
                    let fact = self.ex(st, i, true);
                    st.pc.push(fact);
                }
                let c = self.ex(st, cond, false);
                let mut b = st.clone();
                b.pc.push(c.clone());
                let d0 = self.ex(&mut b, dec, true);
                self.obl(&b, "V-TERMINATION", dec.span, format!("(<= 0 {})", d0), "loop measure may be negative while the loop runs".into(), "the decreases expression must be >= 0 whenever the condition holds");
                self.block(&mut b, body);
                if !b.done {
                    for i in invs {
                        let g = self.ex(&mut b, i, true);
                        self.obl(&b, "V-INVARIANT-KEPT", i.span, g, "loop invariant may not be preserved by the body".into(), "strengthen the invariant so it implies itself after one iteration");
                    }
                    let d1 = self.ex(&mut b, dec, true);
                    self.obl(&b, "V-TERMINATION", dec.span, format!("(< {} {})", d1, d0), "loop measure may not strictly decrease".into(), "each iteration must make the decreases expression smaller");
                }
                st.pc.push(format!("(not {})", c));
            }
            StmtK::Return(e) => {
                let r = match e {
                    None => None,
                    Some(e) if self.f.ret == Ty::Arr => Some(self.ex_arr(st, e)),
                    Some(e) => {
                        let v = self.ex(st, e, false);
                        Some(V { ty: self.f.ret, smt: v, len: None })
                    }
                };
                self.check_post(st, r, s.span);
                st.done = true;
            }
            StmtK::Assert(e) => {
                let g = self.ex(st, e, true);
                self.obl(st, "V-ASSERT", s.span, g, "assertion may not hold".into(), "add the facts it depends on as requires clauses or invariants");
            }
            StmtK::Par(branches) => {
                for b in branches {
                    let v = self.ex(st, &b.call, false);
                    let x = self.fresh(&b.name, b.ty, st);
                    st.pc.push(format!("(= {} {})", x, v));
                    st.vars.insert(b.name.clone(), V { ty: b.ty, smt: x, len: None });
                }
            }
            StmtK::Expr(e) => {
                self.ex(st, e, false);
            }
        }
    }

    fn merge(&mut self, st: &mut St, c: &str, t: St, e: St) {
        match (t.done, e.done) {
            (true, true) => {
                st.done = true;
                return;
            }
            (true, false) => {
                *st = e;
                return;
            }
            (false, true) => {
                *st = t;
                return;
            }
            _ => {}
        }
        let base = st.pc.len();
        st.pc.push(format!("(=> {} (and true {}))", c, t.pc[base..].join(" ")));
        st.pc.push(format!("(=> (not {}) (and true {}))", c, e.pc[base..].join(" ")));
        let mut names: Vec<String> = st.vars.keys().cloned().collect();
        names.sort();
        for n in names {
            let (tv, ev) = (&t.vars[&n].smt, &e.vars[&n].smt);
            if tv != ev {
                let ty = st.vars[&n].ty;
                let m = self.fresh(&n, if ty.is_array() { Ty::Arr } else { ty }, st);
                st.pc.push(format!("(= {} (ite {} {} {}))", m, c, tv, ev));
                st.vars.get_mut(&n).unwrap().smt = m;
            } else {
                st.vars.get_mut(&n).unwrap().smt = tv.clone();
            }
        }
    }
}

fn mods_expr(e: &Expr, out: &mut HashSet<String>) {
    match &e.k {
        ExprK::Borrow { name, mutable: true } => {
            out.insert(name.clone());
        }
        ExprK::Call(_, args) => args.iter().for_each(|a| mods_expr(a, out)),
        ExprK::Index(_, i) => mods_expr(i, out),
        ExprK::Unary(_, a) => mods_expr(a, out),
        ExprK::Binary(_, a, b) => {
            mods_expr(a, out);
            mods_expr(b, out);
        }
        _ => {}
    }
}

fn mods_block(b: &Block, out: &mut HashSet<String>) {
    for s in b {
        match &s.k {
            StmtK::Let { init, .. } => mods_expr(init, out),
            StmtK::Assign { name, val } => {
                out.insert(name.clone());
                mods_expr(val, out);
            }
            StmtK::Store { name, idx, val } => {
                out.insert(name.clone());
                mods_expr(idx, out);
                mods_expr(val, out);
            }
            StmtK::If { cond, then, els } => {
                mods_expr(cond, out);
                mods_block(then, out);
                if let Some(e) = els {
                    mods_block(e, out);
                }
            }
            StmtK::While { cond, body, .. } => {
                mods_expr(cond, out);
                mods_block(body, out);
            }
            StmtK::Return(Some(e)) | StmtK::Expr(e) => mods_expr(e, out),
            StmtK::Par(bs) => bs.iter().for_each(|b| mods_expr(&b.call, out)),
            _ => {}
        }
    }
}

const PRELUDE: &str = "(set-option :produce-models true)
(define-fun cdiv ((a Int) (b Int)) Int
  (ite (>= a 0) (ite (> b 0) (div a b) (- (div a (- b))))
                (ite (> b 0) (- (div (- a) b)) (div (- a) (- b)))))
(define-fun cmod ((a Int) (b Int)) Int (- a (* b (cdiv a b))))
";

fn gen_func<'a>(funcs: &'a HashMap<String, &'a Func>, f: &'a Func) -> (String, Vec<Obl>) {
    let mut g = Gen { funcs, f, decls: vec![], obls: vec![], n: 0, dec_entry: None };
    let mut st = St::default();
    for p in &f.params {
        if p.ty.is_array() {
            let a = g.fresh(&p.name, Ty::Arr, &mut st);
            let len = g.fresh_len(&p.name, &mut st);
            st.vars.insert(p.name.clone(), V { ty: p.ty, smt: a, len: Some(len) });
        } else {
            let x = g.fresh(&p.name, p.ty, &mut st);
            st.vars.insert(p.name.clone(), V { ty: p.ty, smt: x, len: None });
        }
    }
    for r in &f.requires {
        let fact = g.ex(&mut st, r, true);
        st.pc.push(fact);
    }
    if let Some(d) = &f.decreases {
        g.dec_entry = Some(g.ex(&mut st, d, true));
    }
    g.block(&mut st, &f.body);
    if !st.done {
        g.check_post(&mut st, None, f.span);
    }
    let mut script = String::from(PRELUDE);
    for d in &g.decls {
        script += d;
        script.push('\n');
    }
    for (i, o) in g.obls.iter().enumerate() {
        script += "(push 1)\n";
        for p in &o.pc {
            script += &format!("(assert {})\n", p);
        }
        script += &format!("(assert (not {}))\n(echo \"@{}\")\n(check-sat)\n", o.goal, i);
        if !o.cex.is_empty() {
            let terms: Vec<&str> = o.cex.iter().map(|(_, t)| t.as_str()).collect();
            script += &format!("(get-value ({}))\n", terms.join(" "));
        }
        script += "(pop 1)\n";
    }
    (script, g.obls)
}

// Minimal s-expression reader for model values.
fn sexprs(s: &str) -> Vec<String> {
    // Returns the top-level items inside the outermost list of a get-value reply.
    let mut items = vec![];
    let mut depth = 0i32;
    let mut cur = String::new();
    for ch in s.chars() {
        match ch {
            '(' => {
                depth += 1;
                if depth >= 2 {
                    cur.push(ch);
                }
            }
            ')' => {
                if depth >= 2 {
                    cur.push(ch);
                }
                depth -= 1;
                if depth == 1 {
                    items.push(cur.trim().to_string());
                    cur.clear();
                }
            }
            c => {
                if depth >= 2 {
                    cur.push(c);
                }
            }
        }
    }
    items
}

fn pretty_value(v: &str) -> String {
    let v = v.trim();
    if let Some(inner) = v.strip_prefix("(-").and_then(|x| x.strip_suffix(')')) {
        return format!("-{}", inner.trim());
    }
    v.to_string()
}

fn model_values(text: &str, cex: &[(String, String)]) -> Vec<(String, String)> {
    let mut out = vec![];
    for (item, (name, term)) in sexprs(text).iter().zip(cex) {
        let _ = term;
        // item is "(<term> <value>)"; the value is its last top-level element.
        let body = item.strip_prefix('(').and_then(|x| x.strip_suffix(')')).unwrap_or(item);
        let (mut depth, mut start, mut last) = (0i32, 0usize, (0usize, body.len()));
        let bytes = body.as_bytes();
        for (i, &c) in bytes.iter().enumerate() {
            match c {
                b'(' => {
                    if depth == 0 {
                        start = i;
                    }
                    depth += 1;
                }
                b')' => {
                    depth -= 1;
                    if depth == 0 {
                        last = (start, i + 1);
                    }
                }
                b' ' if depth == 0 => start = i + 1,
                _ => {
                    if depth == 0 {
                        last = (start, i + 1);
                    }
                }
            }
        }
        out.push((name.clone(), pretty_value(&body[last.0..last.1])));
    }
    out
}

pub struct VResult {
    pub diags: Vec<Diag>,
    pub proved: usize,
}

pub fn z3_path() -> String {
    std::env::var("KEEL_Z3").unwrap_or_else(|_| "z3".into())
}

fn run_z3(script: &str) -> Result<String, String> {
    let mut child = Command::new(z3_path())
        .args(["-in", "-smt2", "-t:10000"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .map_err(|e| format!("could not run z3 ({}); install it or set KEEL_Z3", e))?;
    child.stdin.take().unwrap().write_all(script.as_bytes()).map_err(|e| e.to_string())?;
    let out = child.wait_with_output().map_err(|e| e.to_string())?;
    Ok(String::from_utf8_lossy(&out.stdout).into_owned())
}

pub fn verify(funcs: &[Func], dump_dir: Option<&str>) -> Result<VResult, String> {
    let map: HashMap<String, &Func> = funcs.iter().map(|f| (f.name.clone(), f)).collect();
    let jobs: Vec<(String, Vec<Obl>)> = funcs.iter().map(|f| gen_func(&map, f)).collect();
    if let Some(dir) = dump_dir {
        for (f, (script, _)) in funcs.iter().zip(&jobs) {
            let _ = std::fs::write(format!("{}/{}.smt2", dir, f.name), script);
        }
    }
    // One solver process per function, all in parallel.
    let outputs: Vec<Result<String, String>> = std::thread::scope(|s| {
        let hs: Vec<_> = jobs.iter().map(|(script, obls)| s.spawn(move || if obls.is_empty() { Ok(String::new()) } else { run_z3(script) })).collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let mut diags = vec![];
    let mut proved = 0;
    for ((_, obls), out) in jobs.iter().zip(outputs) {
        let out = out?;
        let mut results: HashMap<usize, (String, String)> = HashMap::new();
        let mut cur: Option<usize> = None;
        for line in out.lines() {
            if let Some(i) = line.strip_prefix('@') {
                cur = i.trim().parse().ok();
                continue;
            }
            if let Some(i) = cur {
                let e = results.entry(i).or_insert((String::new(), String::new()));
                if e.0.is_empty() {
                    e.0 = line.trim().to_string();
                } else if !line.starts_with("(error") {
                    e.1 += line;
                    e.1.push(' ');
                }
            }
        }
        for (i, o) in obls.iter().enumerate() {
            let (status, model) = results.get(&i).cloned().unwrap_or(("unknown".into(), String::new()));
            match status.as_str() {
                "unsat" => proved += 1,
                "sat" => {
                    let mut d = Diag::new(o.code, o.span, o.msg.clone()).hint(o.hint);
                    d.cex = model_values(&model, &o.cex);
                    diags.push(d);
                }
                _ => {
                    diags.push(Diag::new("V-UNKNOWN", o.span, format!("could not prove: {} (solver gave up)", o.msg)).hint(o.hint));
                }
            }
        }
    }
    diags.sort_by_key(|d| (d.span.line, d.span.col));
    Ok(VResult { diags, proved })
}
