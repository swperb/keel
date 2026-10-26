// Verification-condition generator. Each function is symbolically executed;
// every operation that could misbehave at runtime (overflow, out-of-bounds,
// division by zero, contract violation, non-termination) becomes a proof
// obligation discharged by Z3. Anything not proven is a compile error, which
// is what lets codegen emit zero runtime checks.
//
// Beyond safety, the verifier guards against specifications that prove
// nothing: contradictory `requires` clauses (V-VACUOUS) and branches that can
// never run (V-DEAD) are errors, so a proof cannot pass by making its own
// assumptions impossible.
//
// `spec fn` definitions become SMT functions with guarded definitional
// axioms; their bodies are checked for well-formedness and termination,
// which keeps the axioms consistent. `lemma` bodies are ghost code: checked
// like functions (recursion is induction), then erased.

use crate::ast::*;
use crate::diag::Diag;
use std::collections::HashMap;
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

fn app(f: &str, args: &[String]) -> String {
    if args.is_empty() {
        f.to_string()
    } else {
        format!("({} {})", f, args.join(" "))
    }
}

fn sort(ty: Ty) -> String {
    match ty {
        Ty::Bool => "Bool".into(),
        Ty::Named(id) => type_name(id),
        t if t.is_array() => "(Array Int Int)".into(),
        _ => "Int".into(),
    }
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
    /// A reachability check: passes when the path condition is satisfiable.
    reach: bool,
}

/// One array borrow at a call site: which array, exclusive or not, the
/// borrowed index range [lo, hi), and which par branch it came from.
#[derive(Clone)]
struct Borrowed {
    name: String,
    mutable: bool,
    lo: String,
    hi: String,
    branch: usize,
}

enum Out {
    Scalar(String),
    Arr(V),
    Unit,
}

struct Gen<'a> {
    prog: &'a Program,
    funcs: &'a HashMap<String, &'a Func>,
    f: &'a Func,
    decls: Vec<String>,
    obls: Vec<Obl>,
    n: usize,
    dec_entry: Option<String>,
    /// While verifying a `par` block: array borrows per branch, for
    /// cross-branch disjointness obligations.
    par_borrows: Option<Vec<Borrowed>>,
    /// Inside a lemma: all arithmetic is mathematical.
    ghost: bool,
    /// Checking a spec fn body: calls to spec fns must meet their requires.
    wf: bool,
}

impl<'a> Gen<'a> {
    fn ranges(&self, term: &str, ty: Ty, out: &mut Vec<String>) {
        match ty {
            Ty::I64 => out.push(in_range(term)),
            Ty::Named(id) => match &self.prog.def(id).kind {
                TypeKind::Struct(fs) => {
                    for f in fs {
                        self.ranges(&format!("({}.{} {})", type_name(id), f.name, term), f.ty, out);
                    }
                }
                TypeKind::Enum(vs) => {
                    for v in vs {
                        for f in &v.fields {
                            self.ranges(&format!("({}.{}.{} {})", type_name(id), v.name, f.name, term), f.ty, out);
                        }
                    }
                }
            },
            _ => {}
        }
    }

    fn fresh(&mut self, base: &str, ty: Ty, st: &mut St) -> String {
        self.n += 1;
        let name = format!("v.{}.{}", base, self.n);
        self.decls.push(format!("(declare-const {} {})", name, sort(ty)));
        // Ghost values (lemmas, spec fns) are mathematical integers: no i64 bounds.
        if !(self.ghost || self.wf) {
            let mut rs = vec![];
            self.ranges(&name, ty, &mut rs);
            st.pc.extend(rs);
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
                Ty::I64 | Ty::Bool | Ty::Named(_) => cex.push((k.clone(), v.smt.clone())),
                Ty::Payload(..) | Ty::Unit => {}
                _ => {
                    if let Some(l) = &v.len {
                        cex.push((format!("len({})", k), l.clone()));
                    }
                }
            }
        }
        cex.sort();
        self.obls.push(Obl { code, msg, hint, span, pc: st.pc.clone(), goal, cex, reach: false });
    }

    /// Require that the current path is satisfiable (it can actually happen).
    fn reach(&mut self, st: &St, code: &'static str, span: Span, msg: &str, hint: &'static str) {
        self.obls.push(Obl { code, msg: msg.into(), hint, span, pc: st.pc.clone(), goal: "false".into(), cex: vec![], reach: true });
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
        let spec = spec || self.ghost;
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
                            self.obl(st, "V-OVERFLOW", e.span, in_range(&t), format!("'{}' may overflow i64", op.sym()), "bound the operands with requires clauses or loop invariants");
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
                // Also a constant, so obligations raised inside the body (spec
                // fn calls) hold for an arbitrary in-range value of the variable.
                self.decls.push(format!("(declare-const {} Int)", q));
                st.vars.insert(var.clone(), V { ty: Ty::I64, smt: q.clone(), len: None });
                let range = format!("(and (<= {} {}) (< {} {}))", lv, q, q, hv);
                let bv = self.ex_under(st, &range, body, true);
                st.vars.remove(var);
                if *forall {
                    format!("(forall (({} Int)) (=> {} {}))", q, range, bv)
                } else {
                    format!("(exists (({} Int)) (and {} {}))", q, range, bv)
                }
            }
            ExprK::IfE(c, a, b) => {
                let cv = self.ex(st, c, true);
                let av = self.ex_under(st, &cv, a, true);
                let bv = self.ex_under(st, &format!("(not {})", cv), b, true);
                format!("(ite {} {} {})", cv, av, bv)
            }
            ExprK::Lit { ty, variant, fields } => {
                let args: Vec<String> = fields.iter().map(|(_, fe)| self.ex(st, fe, spec)).collect();
                let ctor = match variant {
                    None => type_name(*ty),
                    Some(v) => format!("{}.{}", type_name(*ty), v),
                };
                app(&ctor, &args)
            }
            ExprK::Field(base, f) => {
                let bt = self.ty_of(st, base);
                let bv = self.ex(st, base, spec);
                match bt {
                    Ty::Named(id) => format!("({}.{} {})", type_name(id), f, bv),
                    Ty::Payload(id, vi) => {
                        let vname = &self.prog.variants(id).unwrap()[vi as usize].name;
                        format!("({}.{}.{} {})", type_name(id), vname, f, bv)
                    }
                    _ => unreachable!("checked"),
                }
            }
            ExprK::As(base, _, _) => self.ex(st, base, spec),
            ExprK::Is(base, id, v) => {
                let bv = self.ex(st, base, spec);
                format!("((_ is {}.{}) {})", type_name(*id), v, bv)
            }
            ExprK::Call(name, args) => match self.call(st, name, args, e.span, spec) {
                Out::Scalar(s) => s,
                Out::Unit => "true".into(),
                Out::Arr(_) => unreachable!("checked"),
            },
        }
    }

    /// Static type of an expression whose type is a struct/enum/payload
    /// (only needed to pick the right field accessor).
    fn ty_of(&self, st: &St, e: &Expr) -> Ty {
        match &e.k {
            ExprK::Var(n) => st.vars[n].ty,
            ExprK::Result => st.vars["result"].ty,
            ExprK::Lit { ty, .. } => Ty::Named(*ty),
            ExprK::Field(b, f) => {
                let bt = self.ty_of(st, b);
                self.prog.fields_of(bt).and_then(|fs| fs.iter().find(|x| x.name == *f)).map(|x| x.ty).unwrap()
            }
            ExprK::Call(n, _) => self.funcs[n.as_str()].ret,
            ExprK::IfE(_, a, _) => self.ty_of(st, a),
            ExprK::As(_, id, v) => {
                let vi = self.prog.variants(*id).unwrap().iter().position(|x| x.name == *v).unwrap();
                Ty::Payload(*id, vi as u32)
            }
            _ => Ty::I64,
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
                self.obl(st, "V-ALLOC", span, format!("(and (<= 0 {}) (<= {} {}))", nv, nv, MAX_LEN), "array length may be negative or larger than 2^40".into(), "bound the length with a requires clause");
                let a = self.fresh("arr", Ty::Arr, st);
                let len = self.fresh_len("arr", st);
                st.pc.push(format!("(= {} ((as const (Array Int Int)) {}))", a, fill));
                st.pc.push(format!("(= {} {})", len, nv));
                return Out::Arr(V { ty: Ty::Arr, smt: a, len: Some(len) });
            }
            _ => {}
        }
        let g = self.funcs[name];
        // Lemma and spec fn arguments are specifications: no runtime obligations.
        let arg_spec = spec || g.kind != FnKind::Code;
        let mut cs = St::default();
        let mut flat: Vec<String> = vec![];
        // (caller array, callee param, slice range if any)
        let mut mut_args: Vec<(String, String, Option<(String, String)>)> = vec![];
        let mut borrowed: Vec<Borrowed> = vec![];
        for (a, p) in args.iter().zip(&g.params) {
            if p.ty.is_array() {
                let ExprK::Borrow { name: an, mutable, range } = &a.k else { unreachable!() };
                let v = st.vars[an].clone();
                let len = v.len.clone().unwrap();
                let (view, vlen, r) = match range {
                    None => (v.smt.clone(), len.clone(), None),
                    Some((lo, hi)) => {
                        let lv = self.ex(st, lo, arg_spec);
                        let hv = self.ex(st, hi, arg_spec);
                        self.obl(
                            st,
                            "V-SLICE",
                            a.span,
                            format!("(and (<= 0 {}) (<= {} {}) (<= {} {}))", lv, lv, hv, hv, len),
                            format!("slice of '{}' may be out of range", an),
                            "prove 0 <= lo <= hi <= len(array) for the slice bounds",
                        );
                        let view = format!("(lambda ((i Int)) (select {} (+ i {})))", v.smt, lv);
                        (view, format!("(- {} {})", hv, lv), Some((lv, hv)))
                    }
                };
                let (blo, bhi) = r.clone().unwrap_or(("0".into(), len.clone()));
                borrowed.push(Borrowed { name: an.clone(), mutable: *mutable, lo: blo, hi: bhi, branch: 0 });
                flat.push(view.clone());
                flat.push(vlen.clone());
                cs.vars.insert(p.name.clone(), V { ty: p.ty, smt: view, len: Some(vlen) });
                if p.ty == Ty::RefMut {
                    mut_args.push((an.clone(), p.name.clone(), r));
                }
            } else {
                let s = self.ex(st, a, arg_spec);
                flat.push(s.clone());
                cs.vars.insert(p.name.clone(), V { ty: p.ty, smt: s, len: None });
            }
        }
        self.disjoint(st, &borrowed, span, "in this call");
        if let Some(pb) = &mut self.par_borrows {
            pb.extend(borrowed);
        }
        let check_pre = g.kind != FnKind::Spec || self.wf;
        if check_pre {
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
        }
        if g.kind == FnKind::Spec {
            return Out::Scalar(app(&format!("sf.{}", name), &flat));
        }
        for (an, pn, r) in mut_args {
            let post = self.fresh(&an, Ty::Arr, st);
            cs.vars.get_mut(&pn).unwrap().smt = post.clone();
            match r {
                None => st.vars.get_mut(&an).unwrap().smt = post,
                Some((lo, hi)) => {
                    // Write the callee's view back into [lo, hi); the rest is unchanged.
                    let old = st.vars[&an].smt.clone();
                    let a2 = self.fresh(&an, Ty::Arr, st);
                    st.pc.push(format!(
                        "(= {} (lambda ((i Int)) (ite (and (<= {} i) (< i {})) (select {} (- i {})) (select {} i))))",
                        a2, lo, hi, post, lo, old
                    ));
                    st.vars.get_mut(&an).unwrap().smt = a2;
                }
            }
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

    /// Prove every pair of borrows of one array that involves an exclusive
    /// borrow touches disjoint index ranges.
    fn disjoint(&mut self, st: &St, bs: &[Borrowed], span: Span, place: &str) {
        for i in 0..bs.len() {
            for j in i + 1..bs.len() {
                let (a, b) = (&bs[i], &bs[j]);
                if a.name != b.name || !(a.mutable || b.mutable) || a.branch != b.branch && place == "in this call" {
                    continue;
                }
                if place != "in this call" && a.branch == b.branch {
                    continue; // same branch: already checked within its call
                }
                self.obl(
                    st,
                    "V-DISJOINT",
                    span,
                    format!("(or (<= {} {}) (<= {} {}) (<= {} {}) (<= {} {}))", a.hi, b.lo, b.hi, a.lo, a.hi, a.lo, b.hi, b.lo),
                    format!("borrows of '{}' {} may overlap (data race)", a.name, place),
                    "make the slice ranges disjoint, e.g. [lo..mid] and [mid..hi]",
                );
            }
        }
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

    fn dead_check(&mut self, st: &St, b: &Block, what: &str) {
        let span = b.first().map(|s| s.span);
        if let Some(span) = span {
            self.reach(st, "V-DEAD", span, &format!("this {} can never execute", what), "delete it, or fix the condition or invariants that make it impossible");
        }
    }

    /// Rebuild a struct value with the field at `path` replaced.
    fn update(&self, term: &str, ty: Ty, path: &[String], val: &str) -> String {
        if path.is_empty() {
            return val.to_string();
        }
        let Ty::Named(id) = ty else { unreachable!() };
        let fs = self.prog.struct_fields(id).unwrap();
        let tn = type_name(id);
        let args: Vec<String> = fs
            .iter()
            .map(|f| {
                let cur = format!("({}.{} {})", tn, f.name, term);
                if f.name == path[0] {
                    self.update(&cur, f.ty, &path[1..], val)
                } else {
                    cur
                }
            })
            .collect();
        app(&tn, &args)
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
            StmtK::Assign { name, path, val } => {
                let v = self.ex(st, val, false);
                let cur = st.vars[name].clone();
                let newv = self.update(&cur.smt, cur.ty, path, &v);
                let x = self.fresh(name, cur.ty, st);
                st.pc.push(format!("(= {} {})", x, newv));
                st.vars.get_mut(name).unwrap().smt = x;
            }
            StmtK::Store { name, idx, val } => {
                let iv = self.ex(st, idx, false);
                let len = st.vars[name].len.clone().unwrap();
                self.obl(
                    st,
                    "V-BOUNDS",
                    s.span,
                    format!("(and (<= 0 {}) (< {} {}))", iv, iv, len),
                    format!("write to '{}' may be out of bounds", name),
                    "prove 0 <= index < len(array) with a requires clause or loop invariant",
                );
                let vv = self.ex(st, val, false);
                // Read the array only after the value: evaluating it may have
                // changed the array (C stores into the array as it is then).
                let a = st.vars[name].clone();
                let a2 = self.fresh(name, Ty::Arr, st);
                st.pc.push(format!("(= {} (store {} {} {}))", a2, a.smt, iv, vv));
                st.vars.get_mut(name).unwrap().smt = a2;
            }
            StmtK::If { cond, then, els } => {
                let c = self.ex(st, cond, false);
                let mut t = st.clone();
                t.pc.push(c.clone());
                self.dead_check(&t, then, "branch");
                self.block(&mut t, then);
                let mut e = st.clone();
                let nc = format!("(not {})", c);
                e.pc.push(nc.clone());
                if let Some(eb) = els {
                    self.dead_check(&e, eb, "else branch");
                    self.block(&mut e, eb);
                }
                self.merge(st, vec![(c, t), (nc, e)]);
            }
            StmtK::Match { scrut, enum_id, arms } => {
                let sv = self.ex(st, scrut, false);
                let tn = type_name(*enum_id);
                let mut outs = vec![];
                for (i, a) in arms.iter().enumerate() {
                    let c = format!("((_ is {}.{}) {})", tn, a.variant, sv);
                    let mut b = st.clone();
                    b.pc.push(c.clone());
                    self.dead_check(&b, &a.body, "match arm");
                    if let Some(bn) = &a.binder {
                        b.vars.insert(bn.clone(), V { ty: Ty::Payload(*enum_id, i as u32), smt: sv.clone(), len: None });
                    }
                    self.block(&mut b, &a.body);
                    if let Some(bn) = &a.binder {
                        b.vars.remove(bn);
                    }
                    outs.push((c, b));
                }
                self.merge(st, outs);
            }
            StmtK::While { cond, invs, dec, body } => {
                for i in invs {
                    let g = self.ex(st, i, true);
                    self.obl(st, "V-INVARIANT-ENTRY", i.span, g, "loop invariant may not hold on entry".into(), "initialize variables so the invariant holds before the first iteration");
                }
                let mut mods = std::collections::HashSet::new();
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
                self.dead_check(&b, body, "loop body");
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
                self.obl(st, "V-ASSERT", s.span, g.clone(), "assertion may not hold".into(), "add the facts it depends on as requires clauses or invariants");
                // A proven assert is a fact for the rest of the path.
                st.pc.push(g);
            }
            StmtK::Par(branches) => {
                // Branches are verified in sequence; that is sound because every
                // pair of array borrows across branches is proven disjoint below.
                let mut all: Vec<Borrowed> = vec![];
                for (bi, b) in branches.iter().enumerate() {
                    self.par_borrows = Some(vec![]);
                    let v = self.ex(st, &b.call, false);
                    let mine = self.par_borrows.take().unwrap();
                    all.extend(mine.into_iter().map(|mut x| {
                        x.branch = bi;
                        x
                    }));
                    if let Some(n) = &b.name {
                        let x = self.fresh(n, b.ty, st);
                        st.pc.push(format!("(= {} {})", x, v));
                        st.vars.insert(n.clone(), V { ty: b.ty, smt: x, len: None });
                    }
                }
                self.disjoint(st, &all, s.span, "across par branches");
            }
            StmtK::Expr(e) => {
                self.ex(st, e, false);
            }
        }
    }

    /// Join the states of mutually exclusive, exhaustive branches.
    fn merge(&mut self, st: &mut St, outs: Vec<(String, St)>) {
        let live: Vec<(String, St)> = outs.into_iter().filter(|(_, s)| !s.done).collect();
        if live.is_empty() {
            st.done = true;
            return;
        }
        if live.len() == 1 {
            *st = live.into_iter().next().unwrap().1;
            return;
        }
        let base = st.pc.len();
        let conds: Vec<&str> = live.iter().map(|(c, _)| c.as_str()).collect();
        let any = format!("(or {})", conds.join(" "));
        for (c, s) in &live {
            st.pc.push(format!("(=> {} (and true {}))", c, s.pc[base..].join(" ")));
        }
        st.pc.push(any);
        let mut names: Vec<String> = st.vars.keys().cloned().collect();
        names.sort();
        for n in names {
            let vals: Vec<&String> = live.iter().map(|(_, s)| &s.vars[&n].smt).collect();
            if vals.iter().all(|v| *v == vals[0]) {
                st.vars.get_mut(&n).unwrap().smt = vals[0].clone();
                continue;
            }
            let ty = st.vars[&n].ty;
            let m = self.fresh(&n, if ty.is_array() { Ty::Arr } else { ty }, st);
            for (c, s) in &live {
                st.pc.push(format!("(=> {} (= {} {}))", c, m, s.vars[&n].smt));
            }
            st.vars.get_mut(&n).unwrap().smt = m;
        }
    }
}

fn mods_expr(e: &Expr, out: &mut std::collections::HashSet<String>) {
    match &e.k {
        ExprK::Borrow { name, mutable: true, .. } => {
            out.insert(name.clone());
        }
        ExprK::Call(_, args) => args.iter().for_each(|a| mods_expr(a, out)),
        ExprK::Index(_, i) => mods_expr(i, out),
        ExprK::Unary(_, a) | ExprK::Field(a, _) | ExprK::Is(a, _, _) | ExprK::As(a, _, _) => mods_expr(a, out),
        ExprK::Binary(_, a, b) => {
            mods_expr(a, out);
            mods_expr(b, out);
        }
        ExprK::Lit { fields, .. } => fields.iter().for_each(|(_, f)| mods_expr(f, out)),
        _ => {}
    }
}

fn mods_block(b: &Block, out: &mut std::collections::HashSet<String>) {
    for s in b {
        match &s.k {
            StmtK::Let { init, .. } => mods_expr(init, out),
            StmtK::Assign { name, val, .. } => {
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
            StmtK::Match { scrut, arms, .. } => {
                mods_expr(scrut, out);
                arms.iter().for_each(|a| mods_block(&a.body, out));
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

/// SMT declarations shared by every function: datatypes for structs and
/// enums, and spec fns with their definitional axioms.
fn shared_prelude(prog: &Program, map: &HashMap<String, &Func>, axioms: bool) -> String {
    let mut s = String::from(PRELUDE);
    if !prog.types.is_empty() {
        let heads: Vec<String> = prog.types.iter().map(|d| format!("({} 0)", d.name)).collect();
        let bodies: Vec<String> = prog
            .types
            .iter()
            .map(|d| {
                let ctor = |cname: String, fs: &Vec<Field>, prefix: &str| {
                    let accs: Vec<String> = fs.iter().map(|f| format!("({}.{} {})", prefix, f.name, sort(f.ty))).collect();
                    if accs.is_empty() {
                        format!("({})", cname)
                    } else {
                        format!("({} {})", cname, accs.join(" "))
                    }
                };
                match &d.kind {
                    TypeKind::Struct(fs) => format!("({})", ctor(d.name.clone(), fs, &d.name)),
                    TypeKind::Enum(vs) => {
                        let cs: Vec<String> = vs.iter().map(|v| ctor(format!("{}.{}", d.name, v.name), &v.fields, &format!("{}.{}", d.name, v.name))).collect();
                        format!("({})", cs.join(" "))
                    }
                }
            })
            .collect();
        s += &format!("(declare-datatypes ({}) ({}))\n", heads.join(" "), bodies.join(" "));
    }
    // Declare all spec fns first so axioms may reference each other.
    let specs: Vec<&Func> = prog.funcs.iter().filter(|f| f.kind == FnKind::Spec).collect();
    for f in &specs {
        let mut sorts = vec![];
        for p in &f.params {
            sorts.push(sort(p.ty));
            if p.ty.is_array() {
                sorts.push("Int".into());
            }
        }
        s += &format!("(declare-fun sf.{} ({}) {})\n", f.name, sorts.join(" "), sort(f.ret));
    }
    // Spec fns are checked without any definitional axioms, so a bad
    // definition can never vouch for its own well-formedness.
    let specs: Vec<&Func> = if axioms { specs } else { vec![] };
    for f in &specs {
        let mut g = Gen { prog, funcs: map, f, decls: vec![], obls: vec![], n: 0, dec_entry: None, par_borrows: None, ghost: true, wf: false };
        let mut st = St::default();
        let mut binders = vec![];
        let mut flat = vec![];
        for p in &f.params {
            let x = format!("p.{}", p.name);
            binders.push(format!("({} {})", x, sort(p.ty)));
            flat.push(x.clone());
            let len = if p.ty.is_array() {
                let l = format!("p.{}.len", p.name);
                binders.push(format!("({} Int)", l));
                flat.push(l.clone());
                Some(l)
            } else {
                None
            };
            st.vars.insert(p.name.clone(), V { ty: p.ty, smt: x, len });
        }
        let pre: Vec<String> = f.requires.iter().map(|r| g.ex(&mut st, r, true)).collect();
        let StmtK::Return(Some(body)) = &f.body[0].k else { unreachable!() };
        let bv = g.ex(&mut st, body, true);
        let call = app(&format!("sf.{}", f.name), &flat);
        let axiom = format!("(=> (and true {}) (= {} {}))", pre.join(" "), call, bv);
        if binders.is_empty() {
            s += &format!("(assert {})\n", axiom);
        } else {
            s += &format!("(assert (forall ({}) (! {} :pattern ({}))))\n", binders.join(" "), axiom, call);
        }
    }
    s
}

fn gen_func<'a>(prog: &'a Program, map: &'a HashMap<String, &'a Func>, f: &'a Func) -> (Vec<String>, Vec<Obl>) {
    let mut g = Gen { prog, funcs: map, f, decls: vec![], obls: vec![], n: 0, dec_entry: None, par_borrows: None, ghost: f.kind == FnKind::Lemma, wf: f.kind == FnKind::Spec };
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
    g.reach(&st, "V-VACUOUS", f.span, &format!("the requires clauses of '{}' contradict each other, so every proof about it would be vacuous", f.name), "no input satisfies these preconditions; fix them");
    if let Some(d) = &f.decreases {
        g.dec_entry = Some(g.ex(&mut st, d, true));
    }
    if f.kind == FnKind::Spec {
        // Well-formedness: evaluate the body so recursive calls are checked.
        let StmtK::Return(Some(body)) = &f.body[0].k else { unreachable!() };
        g.ex(&mut st, body, true);
    } else {
        g.block(&mut st, &f.body);
        if !st.done {
            g.check_post(&mut st, None, f.span);
        }
    }
    (g.decls, g.obls)
}

/// Facts the retry pass drops: quantifiers and array lambdas, which defeat
/// the solver's model search. Dropping facts can only weaken assumptions.
fn is_quantified(fact: &str) -> bool {
    fact.contains("(forall") || fact.contains("(exists") || fact.contains("(lambda")
}

/// One solver script for a function. `pick` selects which obligations to
/// include; with `quant_free`, quantified path facts are dropped.
fn build_script(prelude: &str, decls: &[String], obls: &[Obl], pick: &[usize], quant_free: bool) -> String {
    let mut script = String::from(prelude);
    for d in decls {
        script += d;
        script.push('\n');
    }
    for &i in pick {
        let o = &obls[i];
        script += "(push 1)\n";
        for p in &o.pc {
            if quant_free && is_quantified(p) {
                continue;
            }
            script += &format!("(assert {})\n", p);
        }
        if !o.reach {
            script += &format!("(assert (not {}))\n", o.goal);
        }
        // Reachability needs a model, which quantified axioms make expensive;
        // give it a short budget and report inconclusive results.
        if o.reach {
            script += "(set-option :timeout 300)\n";
        }
        script += &format!("(echo \"@{}\")\n(check-sat)\n", i);
        if o.reach {
            script += "(set-option :timeout 10000)\n";
        }
        if !o.cex.is_empty() && !o.reach {
            let terms: Vec<&str> = o.cex.iter().map(|(_, t)| t.as_str()).collect();
            script += &format!("(get-value ({}))\n", terms.join(" "));
        }
        script += "(pop 1)\n";
    }
    script
}

/// The first solver error in an output, if any. Z3 skips a command it
/// rejects and carries on, so an ill-formed fact or goal would otherwise be
/// silently dropped. (A failed get-value after a proof is expected.)
fn solver_error(out: &str) -> Option<String> {
    out.lines().find(|l| l.starts_with("(error") && !l.contains("model is not available")).map(|l| l.to_string())
}

/// Map obligation index to (status, model text) from solver output.
fn parse_results(out: &str) -> HashMap<usize, (String, String)> {
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
    results
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
        if !inner.contains('(') {
            return format!("-{}", inner.trim());
        }
    }
    v.to_string()
}

fn model_values(text: &str, cex: &[(String, String)]) -> Vec<(String, String)> {
    let mut out = vec![];
    for (item, (name, _)) in sexprs(text).iter().zip(cex) {
        // item is "(<term> <value>)"; the value is its last top-level element.
        let body = item.strip_prefix('(').and_then(|x| x.strip_suffix(')')).unwrap_or(item);
        let (mut depth, mut start, mut last) = (0i32, 0usize, (0usize, body.len()));
        for (i, &c) in body.as_bytes().iter().enumerate() {
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
                b' ' | b'\n' if depth == 0 => start = i + 1,
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
    /// Reachability checks the solver could not settle within budget.
    pub inconclusive: usize,
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

pub fn verify(prog: &Program, dump_dir: Option<&str>) -> Result<VResult, String> {
    let funcs = &prog.funcs;
    let map: HashMap<String, &Func> = funcs.iter().map(|f| (f.name.clone(), f)).collect();
    // Phase 1: spec fn definitions (no axioms). Phase 2: everything else,
    // only once every definition is known to be well-founded.
    let (specs, rest): (Vec<&Func>, Vec<&Func>) = funcs.iter().partition(|f| f.kind == FnKind::Spec);
    let mut total = VResult { diags: vec![], proved: 0, inconclusive: 0 };
    for (phase, axioms) in [(specs, false), (rest, true)] {
        let prelude = shared_prelude(prog, &map, axioms);
        let bare = shared_prelude(prog, &map, false);
        let r = run_phase(prog, &map, &phase, &prelude, &bare, dump_dir)?;
        total.proved += r.proved;
        total.inconclusive += r.inconclusive;
        total.diags.extend(r.diags);
        if !total.diags.is_empty() {
            break;
        }
    }
    Ok(total)
}

fn run_phase(prog: &Program, map: &HashMap<String, &Func>, funcs: &[&Func], prelude: &str, bare: &str, dump_dir: Option<&str>) -> Result<VResult, String> {
    let jobs: Vec<(Vec<String>, Vec<Obl>)> = funcs.iter().map(|f| gen_func(prog, map, f)).collect();
    let scripts: Vec<String> = jobs.iter().map(|(d, o)| build_script(prelude, d, o, &(0..o.len()).collect::<Vec<_>>(), false)).collect();
    if let Some(dir) = dump_dir {
        for (f, script) in funcs.iter().zip(&scripts) {
            let _ = std::fs::write(format!("{}/{}.smt2", dir, f.name), script);
        }
    }
    // One solver process per function, all in parallel.
    let outputs: Vec<Result<String, String>> = std::thread::scope(|s| {
        let hs: Vec<_> = scripts.iter().zip(&jobs).map(|(script, (_, obls))| s.spawn(move || if obls.is_empty() { Ok(String::new()) } else { run_z3(script) })).collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let mut first: Vec<HashMap<usize, (String, String)>> = vec![];
    let mut errors: Vec<Option<String>> = vec![];
    for out in outputs {
        let out = out?;
        errors.push(solver_error(&out));
        first.push(parse_results(&out));
    }
    // Second pass for proof obligations the solver gave up on: retry without
    // quantified facts or definitional axioms. Dropping assumptions is sound
    // for proving (unsat with fewer facts implies unsat with all of them); a
    // model found this way is reported as a candidate counterexample.
    let retry: Vec<Vec<usize>> = jobs
        .iter()
        .zip(&first)
        .map(|((_, obls), res)| (0..obls.len()).filter(|&i| !obls[i].reach && res.get(&i).map(|r| r.0 != "sat" && r.0 != "unsat").unwrap_or(true)).collect())
        .collect();
    let second: Vec<(HashMap<usize, (String, String)>, Option<String>)> = std::thread::scope(|s| {
        let hs: Vec<_> = jobs
            .iter()
            .zip(&retry)
            .map(|((d, o), pick)| {
                s.spawn(move || {
                    if pick.is_empty() {
                        (HashMap::new(), None)
                    } else {
                        run_z3(&build_script(bare, d, o, pick, true)).map(|out| (parse_results(&out), solver_error(&out))).unwrap_or_default()
                    }
                })
            })
            .collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let (second, errors2): (Vec<HashMap<usize, (String, String)>>, Vec<Option<String>>) = second.into_iter().unzip();
    let mut diags = vec![];
    let mut proved = 0;
    let mut inconclusive = 0;
    for (k, f) in funcs.iter().enumerate() {
        if let Some(e) = errors[k].as_ref().or(errors2[k].as_ref()) {
            diags.push(Diag::new("V-UNKNOWN", f.span, format!("solver rejected part of the proof script for '{}', so its results cannot be trusted: {}", f.name, e)).hint("this is a keel bug; please report it with the program"));
        }
    }
    for (((_, obls), res1), res2) in jobs.iter().zip(&first).zip(&second) {
        for (i, o) in obls.iter().enumerate() {
            let (status, model) = res1.get(&i).cloned().unwrap_or(("unknown".into(), String::new()));
            match (o.reach, status.as_str()) {
                (false, "unsat") | (true, "sat") => proved += 1,
                (true, "unsat") => diags.push(Diag::new(o.code, o.span, o.msg.clone()).hint(o.hint)),
                (true, _) => inconclusive += 1, // not a proof failure, but reported
                (false, "sat") => {
                    let mut d = Diag::new(o.code, o.span, o.msg.clone()).hint(o.hint);
                    d.cex = model_values(&model, &o.cex);
                    diags.push(d);
                }
                (false, other) => match res2.get(&i).map(|r| (r.0.as_str(), r.1.clone())) {
                    Some(("unsat", _)) => proved += 1,
                    Some(("sat", m)) => {
                        let mut d = Diag::new(o.code, o.span, format!("{} (counterexample ignores quantified facts; it may be spurious)", o.msg)).hint(o.hint);
                        d.cex = model_values(&m, &o.cex);
                        diags.push(d);
                    }
                    _ => {
                        let why = if other.starts_with("(error") { format!("solver error: {}", other) } else { "solver gave up".into() };
                        diags.push(Diag::new("V-UNKNOWN", o.span, format!("could not prove: {} ({})", o.msg, why)).hint(o.hint));
                    }
                },
            }
        }
    }
    diags.sort_by_key(|d| (d.span.line, d.span.col));
    Ok(VResult { diags, proved, inconclusive })
}
