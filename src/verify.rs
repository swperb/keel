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
use std::sync::atomic::{AtomicBool, Ordering};

/// Whether the program uses the built-in `count`; its theory is only sent
/// to the solver when needed.
static USES_COUNT: AtomicBool = AtomicBool::new(false);

fn uses_count() -> bool {
    USES_COUNT.load(Ordering::Relaxed)
}

/// Whether the program uses bitwise operators; their bit-vector
/// definitions are only sent to the solver when needed.
static USES_BITS: AtomicBool = AtomicBool::new(false);

/// Bitwise operators on integers, through 64-bit vectors. `k.bv` wraps an
/// integer to 64 bits and `k.s64` reads a vector back as two's complement,
/// so on i64 values these are exactly C's operators. `k.pow2` is 2^b for
/// 0 <= b < 64 (and 0 otherwise; code proves the range).
const BITS_DECLS: &str = "(define-fun k.s64 ((x (_ BitVec 64))) Int
  (let ((n (bv2nat x))) (ite (>= n 9223372036854775808) (- n 18446744073709551616) n)))
(define-fun k.bv ((a Int)) (_ BitVec 64) ((_ int2bv 64) a))
(define-fun k.pow2 ((b Int)) Int
  (ite (and (<= 0 b) (< b 64)) (bv2nat (bvshl #x0000000000000001 (k.bv b))) 0))
";

/// The built-in multiset theory behind `count(&xs, lo, hi, v)`: the number
/// of indices i in [lo, hi) with xs[i] == v. Its definition unfolds through
/// a fuel argument (two steps per use), which keeps the solver out of
/// matching loops; the remaining axioms are standard lemmas about it
/// (splitting a range, a single store), trusted like the solver itself.
const COUNT_DECLS: &str = "(declare-datatypes ((K.Fuel 0)) (((K.Z) (K.S (K.prev K.Fuel)))))
(declare-fun kcount (K.Fuel (Array Int Int) Int Int Int) Int)
";

const COUNT_THEORY: &str = "(assert (forall ((f K.Fuel) (a (Array Int Int)) (l Int) (h Int) (v Int))
  (! (= (kcount (K.S f) a l h v) (kcount f a l h v)) :pattern ((kcount (K.S f) a l h v)))))
(assert (forall ((f K.Fuel) (a (Array Int Int)) (l Int) (h Int) (v Int))
  (! (= (kcount (K.S f) a l h v)
        (ite (< l h) (+ (kcount f a l (- h 1) v) (ite (= (select a (- h 1)) v) 1 0)) 0))
     :pattern ((kcount (K.S f) a l h v)))))
(assert (forall ((a (Array Int Int)) (l Int) (h Int) (v Int))
  (! (and (>= (kcount K.Z a l h v) 0) (=> (<= h l) (= (kcount K.Z a l h v) 0)))
     :pattern ((kcount K.Z a l h v)))))
(assert (forall ((a (Array Int Int)) (l Int) (m Int) (h Int) (v Int))
  (! (=> (and (<= l m) (<= m h)) (= (kcount K.Z a l h v) (+ (kcount K.Z a l m v) (kcount K.Z a m h v))))
     :pattern ((kcount K.Z a l m v) (kcount K.Z a m h v)))))
(assert (forall ((a (Array Int Int)) (i Int) (x Int) (l Int) (h Int) (v Int))
  (! (= (kcount K.Z (store a i x) l h v)
        (ite (and (<= l i) (< i h))
             (+ (- (kcount K.Z a l h v) (ite (= (select a i) v) 1 0)) (ite (= x v) 1 0))
             (kcount K.Z a l h v)))
     :pattern ((kcount K.Z (store a i x) l h v)))))
";

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

/// `t` is a value of integer type `k`.
fn range_of(t: &str, k: IntK) -> String {
    let (lo, hi) = k.range();
    format!("(and (<= {} {}) (<= {} {}))", lit(lo), t, t, lit(hi))
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

/// How a `par for` iteration touches an array slot range.
#[derive(Clone, Copy, PartialEq)]
enum AKind {
    Read,
    Write,
    /// Read by the loop's `ensures`, which is carried to the final state.
    EnsRead,
}

/// One array access by a `par for` iteration: slots [lo, hi) of `name`
/// (one slot when `hi` is None), on the path `pc`.
struct Access {
    name: String,
    lo: String,
    hi: Option<String>,
    kind: AKind,
    pc: Vec<String>,
    span: Span,
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
    /// Variables on entry, for `old(..)`. At a call site, the callee's pre-state.
    entry: HashMap<String, V>,
    /// Quantifiers enclosing the expression being translated. Under one, a
    /// term may mention a bound variable, so it cannot be named by a
    /// top-level constant.
    quant: usize,
    /// Element type of the array an `array(n, fill)` call is bound to.
    arr_elem: IntK,
    /// While verifying a `par for` body: the array accesses of one iteration.
    rec: Option<Vec<Access>>,
    /// Recording the reads of a `par for` ensures (specification reads count).
    rec_ens: bool,
    /// Inside `old(..)`: reads of the entry state are not accesses.
    in_old: usize,
}

impl<'a> Gen<'a> {
    /// Record an access by the current `par for` iteration, if any. Reads
    /// in specifications are ghost and never touch memory, except in the
    /// loop's own ensures.
    fn record(&mut self, st: &St, name: &str, lo: &str, hi: Option<&str>, write: bool, spec: bool, span: Span) {
        if self.in_old > 0 || (spec && !self.rec_ens) {
            return;
        }
        let kind = if write { AKind::Write } else if self.rec_ens { AKind::EnsRead } else { AKind::Read };
        if let Some(r) = &mut self.rec {
            r.push(Access { name: name.to_string(), lo: lo.to_string(), hi: hi.map(|h| h.to_string()), kind, pc: st.pc.clone(), span });
        }
    }

    fn ranges(&self, term: &str, ty: Ty, out: &mut Vec<String>) {
        match ty {
            Ty::Int(k) => out.push(range_of(term, k)),
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

    /// Prove a value stored into a slot of type `ty` fits it. Values are
    /// computed in i64; only narrower integer types need this. Without it,
    /// binding the value would assume its range and make the path vacuous.
    fn fit(&mut self, st: &St, v: &str, ty: Ty, span: Span) {
        if self.ghost || self.wf {
            return;
        }
        if let Some(k) = ty.narrow() {
            let (lo, hi) = k.range();
            let msg = format!("value may not fit in {} ({}..={})", k.name(), lo, hi);
            self.obl(st, "V-OVERFLOW", span, range_of(v, k), msg, "bound the value with a requires clause, a test or an invariant, or use wrap_<type>(..) for modular arithmetic");
        }
    }

    /// The + - * spine of a wrap_<type>(..) argument, unchecked: modular
    /// arithmetic is exact there (C computes it in uint64_t, and 2^N
    /// divides 2^64). Every other operator is translated and checked as
    /// usual.
    fn ex_ring(&mut self, st: &mut St, e: &Expr, spec: bool) -> String {
        match &e.k {
            ExprK::Binary(op @ (BOp::Add | BOp::Sub | BOp::Mul), a, b) => {
                let (x, y) = (self.ex_ring(st, a, spec), self.ex_ring(st, b, spec));
                format!("({} {} {})", match op { BOp::Add => "+", BOp::Sub => "-", _ => "*" }, x, y)
            }
            ExprK::Unary(UOp::Neg, a) => format!("(- {})", self.ex_ring(st, a, spec)),
            _ => self.ex(st, e, spec),
        }
    }

    /// A 64-bit vector naming the bits of integer term `t`.
    fn bits(&mut self, st: &mut St, t: &str) -> String {
        self.n += 1;
        let name = format!("b.{}", self.n);
        self.decls.push(format!("(declare-const {} (_ BitVec 64))", name));
        st.pc.push(format!("(= {} (k.bv {}))", name, t));
        st.pc.push(format!("(=> {} (= {} (k.s64 {})))", in_range(t), t, name));
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
        // Goals unfold `count` twice; the resulting fuel-zero terms are the
        // ones assumptions are stated over, so the two meet in the e-graph.
        let goal = goal.replace("(kcount K.Z ", "(kcount (K.S (K.S K.Z)) ");
        let mut cex: Vec<(String, String)> = vec![];
        for (k, v) in &st.vars {
            match v.ty {
                Ty::Int(_) | Ty::Bool | Ty::Named(_) => cex.push((k.clone(), v.smt.clone())),
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
                self.record(st, n, &iv, None, false, spec, e.span);
                let t = format!("(select {} {})", a.smt, iv);
                if !spec {
                    st.pc.push(range_of(&t, a.ty.elem().unwrap()));
                }
                t
            }
            ExprK::Unary(UOp::Not, a) => format!("(not {})", self.ex(st, a, spec)),
            // ~a == -a - 1 in two's complement; it cannot overflow.
            ExprK::Unary(UOp::BitNot, a) => {
                let av = self.ex(st, a, spec);
                let t = format!("(- (- 1) {})", av);
                // The solver cannot derive this bridge between the integer
                // and its bits on its own; it holds for every integer.
                if self.quant == 0 {
                    let x = self.bits(st, &av);
                    st.pc.push(format!("(= (k.bv {}) (bvnot {}))", t, x));
                }
                t
            }
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
                    BOp::BitAnd | BOp::BitOr | BOp::BitXor => {
                        let f = match op {
                            BOp::BitAnd => "bvand",
                            BOp::BitOr => "bvor",
                            _ => "bvxor",
                        };
                        // A low mask is a remainder: in two's complement,
                        // x & (2^k - 1) == x mod 2^k (non-negative) for every
                        // integer x. Arithmetic keeps such proofs linear.
                        let low_mask = |e: &Expr| match e.k {
                            ExprK::Int(m) if m > 0 && m < I64_MAX && (m + 1) & m == 0 => Some(m + 1),
                            _ => None,
                        };
                        // Packing: when one side is h * 2^k (h << k) and the
                        // other is in [0, 2^k), their bits do not overlap, so
                        // | and ^ are exactly addition. Guarded, so exact.
                        let shifted = |e: &Expr| match &e.k {
                            ExprK::Binary(BOp::Shl, _, k) => match k.k {
                                ExprK::Int(k) if (0..63).contains(&k) => Some(1i128 << k),
                                _ => None,
                            },
                            ExprK::Binary(BOp::Mul, x, y) => [x, y].iter().find_map(|z| match z.k {
                                ExprK::Int(m) if m > 0 && m & (m - 1) == 0 => Some(m),
                                _ => None,
                            }),
                            _ => None,
                        };
                        let pack = match op {
                            BOp::BitOr | BOp::BitXor => shifted(a).map(|m| (m, &bv)).or_else(|| shifted(b).map(|m| (m, &av))),
                            _ => None,
                        };
                        let general = if let (BOp::BitAnd, Some(m)) = (op, low_mask(b).or(low_mask(a))) {
                            let x = if low_mask(b).is_some() { &av } else { &bv };
                            format!("(mod {} {})", x, lit(m))
                        } else if self.quant > 0 {
                            format!("(k.s64 ({} (k.bv {}) (k.bv {})))", f, av, bv)
                        } else {
                            // Name each operand's bits and state that an
                            // in-range operand equals its two's-complement
                            // reading: both facts are true, and the second lets
                            // the solver reason on vectors, not through
                            // int2bv's modulus. Under a quantifier a term may
                            // mention the bound variable, so it stays inline.
                            let x = self.bits(st, &av);
                            let y = self.bits(st, &bv);
                            format!("(k.s64 ({} {} {}))", f, x, y)
                        };
                        match pack {
                            Some((m, lo)) => format!("(ite (and (<= 0 {lo}) (< {lo} {m})) (+ {} {}) {general})", av, bv, lo = lo, m = lit(m), general = general),
                            None => general,
                        }
                    }
                    BOp::Shl | BOp::Shr => {
                        if !spec {
                            self.obl(st, "V-SHIFT", b.span, format!("(and (<= 0 {}) (< {} 64))", bv, bv), format!("shift amount of '{}' may be negative or 64 or more", op.sym()), "prove 0 <= amount < 64");
                            st.pc.push(format!("(and (<= 0 {}) (< {} 64))", bv, bv));
                        }
                        // A literal amount stays linear: a * 8, not a * 2^b.
                        let p = match &b.k {
                            ExprK::Int(n) if (0..64).contains(n) => lit(1i128 << n),
                            _ => format!("(k.pow2 {})", bv),
                        };
                        if *op == BOp::Shl {
                            let t = format!("(* {} {})", av, p);
                            if !spec {
                                self.obl(st, "V-OVERFLOW", e.span, in_range(&t), "'<<' may overflow i64".into(), "bound the operand so the shifted value fits in i64");
                            }
                            t
                        } else {
                            // Arithmetic shift: floor division (SMT div rounds
                            // down for a positive divisor).
                            format!("(div {} {})", av, p)
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
            ExprK::Old(inner) => {
                // Evaluate in the entry state; names bound since (quantifier
                // variables) are carried over.
                let mut pre = St { vars: self.entry.clone(), pc: vec![], done: false };
                for (k, v) in &st.vars {
                    pre.vars.entry(k.clone()).or_insert_with(|| v.clone());
                }
                self.in_old += 1;
                let r = self.ex(&mut pre, inner, true);
                self.in_old -= 1;
                r
            }
            ExprK::Quant { forall, var, range, body } => {
                let bounds = match range {
                    Some((lo, hi)) => Some((self.ex(st, lo, true), self.ex(st, hi, true))),
                    None => None,
                };
                self.n += 1;
                let q = format!("q.{}.{}", var, self.n);
                // Also a constant, so obligations raised inside the body (spec
                // fn calls) hold for an arbitrary in-range value of the variable.
                self.decls.push(format!("(declare-const {} Int)", q));
                st.vars.insert(var.clone(), V { ty: Ty::I64, smt: q.clone(), len: None });
                let range = match bounds {
                    Some((lv, hv)) => format!("(and (<= {} {}) (< {} {}))", lv, q, q, hv),
                    None => in_range(&q),
                };
                self.quant += 1;
                let bv = self.ex_under(st, &range, body, true);
                self.quant -= 1;
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
                let decl: Vec<Ty> = match variant {
                    None => self.prog.struct_fields(*ty).unwrap().iter().map(|f| f.ty).collect(),
                    Some(v) => self.prog.variants(*ty).unwrap().iter().find(|x| x.name == *v).unwrap().fields.iter().map(|f| f.ty).collect(),
                };
                let mut args: Vec<String> = vec![];
                for ((_, fe), fty) in fields.iter().zip(decl) {
                    let v = self.ex(st, fe, spec);
                    if !spec {
                        self.fit(st, &v, fty, fe.span);
                    }
                    args.push(v);
                }
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

    /// An array value bound to type `ty` (an `array(..)` call takes its
    /// element type from there).
    fn ex_arr(&mut self, st: &mut St, e: &Expr, ty: Ty) -> V {
        match &e.k {
            ExprK::Var(n) => st.vars[n].clone(),
            ExprK::Call(name, args) => {
                self.arr_elem = ty.elem().unwrap();
                let out = self.call(st, name, args, e.span, false);
                self.arr_elem = IntK::I64;
                match out {
                    Out::Arr(v) => V { ty, ..v },
                    _ => unreachable!("checked"),
                }
            }
            _ => unreachable!("checked"),
        }
    }

    fn call(&mut self, st: &mut St, name: &str, args: &[Expr], span: Span, spec: bool) -> Out {
        match name {
            "count" => {
                let ExprK::Borrow { name: an, .. } = &args[0].k else { unreachable!("checked") };
                let arr = st.vars[an].smt.clone();
                let lo = self.ex(st, &args[1], true);
                let hi = self.ex(st, &args[2], true);
                let v = self.ex(st, &args[3], true);
                self.record(st, an, &lo, Some(&hi), false, true, span);
                // Facts use fuel zero; obl() gives goals two unfoldings.
                return Out::Scalar(format!("(kcount K.Z {} {} {} {})", arr, lo, hi, v));
            }
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
                let elem = std::mem::replace(&mut self.arr_elem, IntK::I64);
                self.fit(st, &fill, Ty::Int(elem), args[1].span);
                self.obl(st, "V-ALLOC", span, format!("(and (<= 0 {}) (<= {} {}))", nv, nv, MAX_LEN), "array length may be negative or larger than 2^40".into(), "bound the length with a requires clause");
                let a = self.fresh("arr", Ty::Arr, st);
                let len = self.fresh_len("arr", st);
                st.pc.push(format!("(= {} ((as const (Array Int Int)) {}))", a, fill));
                st.pc.push(format!("(= {} {})", len, nv));
                return Out::Arr(V { ty: Ty::Arr, smt: a, len: Some(len) });
            }
            _ => {}
        }
        if let Some(k) = crate::check::wrap_kind(name) {
            let t = self.ex_ring(st, &args[0], spec);
            let m = lit(1i128 << k.bits());
            return Out::Scalar(if k.signed() {
                let h = lit(1i128 << (k.bits() - 1));
                format!("(- (mod (+ {} {}) {}) {})", t, h, m, h)
            } else {
                format!("(mod {} {})", t, m)
            });
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
                        // Name the view so facts about it can be stated and matched.
                        let view = self.fresh(&format!("{}.view", an), Ty::Arr, st);
                        st.pc.push(format!("(= {} (lambda ((i Int)) (select {} (+ i {}))))", view, v.smt, lv));
                        if uses_count() {
                            st.pc.push(format!(
                                "(forall ((l Int) (h Int) (v Int)) (! (= (kcount K.Z {} l h v) (kcount K.Z {} (+ l {}) (+ h {}) v)) :pattern ((kcount K.Z {} l h v))))",
                                view, v.smt, lv, lv, view
                            ));
                        }
                        (view, format!("(- {} {})", hv, lv), Some((lv, hv)))
                    }
                };
                let (blo, bhi) = r.clone().unwrap_or(("0".into(), len.clone()));
                borrowed.push(Borrowed { name: an.clone(), mutable: *mutable, lo: blo, hi: bhi, branch: 0 });
                flat.push(view.clone());
                flat.push(vlen.clone());
                cs.vars.insert(p.name.clone(), V { ty: p.ty, smt: view, len: Some(vlen) });
                if matches!(p.ty, Ty::RefMutOf(_)) {
                    mut_args.push((an.clone(), p.name.clone(), r));
                }
            } else {
                let s = self.ex(st, a, arg_spec);
                if !arg_spec {
                    self.fit(st, &s, p.ty, a.span);
                }
                flat.push(s.clone());
                cs.vars.insert(p.name.clone(), V { ty: p.ty, smt: s, len: None });
            }
        }
        self.disjoint(st, &borrowed, span, "in this call");
        for b in &borrowed {
            self.record(st, &b.name, &b.lo, Some(&b.hi), b.mutable, arg_spec, span);
        }
        if let Some(pb) = &mut self.par_borrows {
            pb.extend(borrowed);
        }
        // The callee's pre-state, for `old(..)` in its ensures.
        let pre_call = cs.vars.clone();
        // A fn called from a specification stands for its lifted definition.
        let as_spec = g.kind == FnKind::Spec || (spec && g.kind == FnKind::Code);
        let check_pre = !as_spec || self.wf;
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
        if as_spec {
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
                    if uses_count() {
                        st.pc.push(format!(
                            "(forall ((l Int) (h Int) (v Int)) (! (and (=> (<= h {lo}) (= (kcount K.Z {a2} l h v) (kcount K.Z {old} l h v))) (=> (<= {hi} l) (= (kcount K.Z {a2} l h v) (kcount K.Z {old} l h v))) (=> (and (<= {lo} l) (<= h {hi})) (= (kcount K.Z {a2} l h v) (kcount K.Z {post} (- l {lo}) (- h {lo}) v)))) :pattern ((kcount K.Z {a2} l h v))))",
                            lo = lo, hi = hi, a2 = a2, old = old, post = post
                        ));
                    }
                    st.vars.get_mut(&an).unwrap().smt = a2;
                }
            }
        }
        let out = match g.ret {
            Ty::Unit => Out::Unit,
            Ty::ArrOf(_) => {
                let a = self.fresh("ret", Ty::Arr, st);
                let len = self.fresh_len("ret", st);
                let v = V { ty: g.ret, smt: a, len: Some(len) };
                cs.vars.insert("result".into(), v.clone());
                Out::Arr(v)
            }
            t => {
                let r = self.fresh(&format!("{}.ret", name), t, st);
                cs.vars.insert("result".into(), V { ty: t, smt: r.clone(), len: None });
                // A liftable fn computes exactly its lifted definition, and
                // its requires were just checked, so the caller learns the
                // value itself, not only the ensures.
                if g.kind == FnKind::Code && crate::lift::why_not(self.funcs, name).is_none() {
                    st.pc.push(format!("(= {} {})", r, app(&format!("sf.{}", name), &flat)));
                }
                Out::Scalar(r)
            }
        };
        let saved = std::mem::replace(&mut self.entry, pre_call);
        for en in &g.ensures {
            let fact = self.ex(&mut cs, en, true);
            st.pc.push(fact);
        }
        self.entry = saved;
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
                if ty.is_owned_array() {
                    let v = self.ex_arr(st, init, *ty);
                    st.vars.insert(name.clone(), v);
                } else {
                    let val = self.ex(st, init, false);
                    self.fit(st, &val, *ty, init.span);
                    let x = self.fresh(name, *ty, st);
                    st.pc.push(format!("(= {} {})", x, val));
                    st.vars.insert(name.clone(), V { ty: *ty, smt: x, len: None });
                }
            }
            StmtK::Assign { name, path, val } => {
                let v = self.ex(st, val, false);
                let cur = st.vars[name].clone();
                let mut slot = cur.ty;
                for f in path {
                    slot = self.prog.fields_of(slot).and_then(|fs| fs.iter().find(|x| x.name == *f)).map(|x| x.ty).unwrap();
                }
                self.fit(st, &v, slot, val.span);
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
                self.fit(st, &vv, Ty::Int(a.ty.elem().unwrap()), val.span);
                self.record(st, name, &iv, None, true, false, s.span);
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
                    Some(e) if self.f.ret.is_owned_array() => Some(self.ex_arr(st, e, self.f.ret)),
                    Some(e) => {
                        let v = self.ex(st, e, false);
                        self.fit(st, &v, self.f.ret, e.span);
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
            StmtK::ParFor { var, lo, hi, ens, body } => self.par_for(st, var, lo, hi, ens, body),
        }
    }

    /// A `par for` (docs/par-for.md). The body is verified once for an
    /// arbitrary iteration i, from the state before the loop. A second
    /// copy, for another iteration j != i, is run only to collect its array
    /// accesses: every slot i writes must be one j neither reads nor
    /// writes, and every slot the ensures reads must be one j does not
    /// write. Then no iteration observes another, so running them in any
    /// order or at once gives the same result as running each from the
    /// state before the loop, and each iteration's ensures still holds at
    /// the end.
    fn par_for(&mut self, st: &mut St, var: &str, lo: &Expr, hi: &Expr, ens: &[Expr], body: &Block) {
        let lov = self.ex(st, lo, false);
        let hiv = self.ex(st, hi, false);
        let base = st.pc.len();
        let range = |x: &str| format!("(and (<= {} {}) (< {} {}))", lov, x, x, hiv);
        let outer = self.rec.take();
        // Iteration i: every obligation of the body, then its ensures.
        let mut a = st.clone();
        let iv = self.fresh(var, Ty::I64, &mut a);
        a.pc.push(range(&iv));
        a.vars.insert(var.to_string(), V { ty: Ty::I64, smt: iv.clone(), len: None });
        self.dead_check(&a, body, "par for body");
        self.rec = Some(vec![]);
        self.block(&mut a, body);
        self.rec_ens = true;
        for e in ens {
            let g = self.ex(&mut a, e, true);
            self.obl(&a, "V-ENSURES", e.span, g, format!("this par for ensures may not hold after iteration '{}'", var), "make the body establish it for its own iteration; it may only mention that iteration's slots of written arrays");
        }
        self.rec_ens = false;
        let acc_i = self.rec.take().unwrap();
        // Iteration j: a renamed copy whose own obligations repeat i's.
        let nobl = self.obls.len();
        let mut b = st.clone();
        let jv = self.fresh(var, Ty::I64, &mut b);
        b.pc.push(range(&jv));
        b.vars.insert(var.to_string(), V { ty: Ty::I64, smt: jv.clone(), len: None });
        self.rec = Some(vec![]);
        self.block(&mut b, body);
        let acc_j = self.rec.take().unwrap();
        self.obls.truncate(nobl);
        self.rec = outer;
        let mut pair = St::default();
        pair.vars.insert(var.to_string(), V { ty: Ty::I64, smt: iv.clone(), len: None });
        pair.vars.insert(format!("{}'", var), V { ty: Ty::I64, smt: jv.clone(), len: None });
        for x in &acc_i {
            for y in &acc_j {
                let what = match (x.kind, y.kind) {
                    (AKind::Write, AKind::Write) => format!("two iterations of this par for may write the same slot of '{}' (data race; the other write is at line {})", x.name, y.span.line),
                    (AKind::Write, AKind::Read) => format!("an iteration may write a slot of '{}' that another iteration reads at line {} (data race)", x.name, y.span.line),
                    (AKind::EnsRead, AKind::Write) => format!("this ensures reads a slot of '{}' that another iteration writes at line {}, so it may not hold once the loop ends", x.name, y.span.line),
                    _ => continue,
                };
                if x.name != y.name {
                    continue;
                }
                pair.pc = x.pc.clone();
                pair.pc.extend(y.pc[base..].iter().cloned());
                pair.pc.push(format!("(not (= {} {}))", iv, jv));
                let goal = match (&x.hi, &y.hi) {
                    (None, None) => format!("(not (= {} {}))", x.lo, y.lo),
                    _ => {
                        let xh = x.hi.clone().unwrap_or_else(|| format!("(+ {} 1)", x.lo));
                        let yh = y.hi.clone().unwrap_or_else(|| format!("(+ {} 1)", y.lo));
                        format!("(or (<= {xh} {yl}) (<= {yh} {xl}) (<= {xh} {xl}) (<= {yh} {yl}))", xh = xh, yh = yh, xl = x.lo, yl = y.lo)
                    }
                };
                self.obl(&pair, "V-RACE", x.span, goal, what, "each iteration may write only slots no other iteration touches, e.g. xs[i] or xs[2 * i + 1]; read other slots only of arrays the loop does not write");
            }
        }
        // After the loop: written arrays are known only through the ensures.
        let mut mods = std::collections::HashSet::new();
        mods_block(body, &mut mods);
        let mut names: Vec<String> = mods.into_iter().filter(|m| st.vars.get(m).is_some_and(|v| v.ty.is_array())).collect();
        names.sort();
        for m in names {
            let x = self.fresh(&m, Ty::Arr, st);
            st.vars.get_mut(&m).unwrap().smt = x;
        }
        for e in ens {
            self.n += 1;
            let q = format!("q.{}.{}", var, self.n);
            self.decls.push(format!("(declare-const {} Int)", q));
            st.vars.insert(var.to_string(), V { ty: Ty::I64, smt: q.clone(), len: None });
            let r = range(&q);
            self.quant += 1;
            let g = self.ex_under(st, &r, e, true);
            self.quant -= 1;
            st.vars.remove(var);
            st.pc.push(format!("(forall (({} Int)) (=> {} {}))", q, r, g));
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
            StmtK::ParFor { body, .. } => mods_block(body, out),
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

fn calls_expr(e: &Expr, out: &mut Vec<String>) {
    match &e.k {
        ExprK::Call(name, args) => {
            out.push(name.clone());
            args.iter().for_each(|a| calls_expr(a, out));
        }
        ExprK::Index(_, a) | ExprK::Unary(_, a) | ExprK::Old(a) | ExprK::Field(a, _) | ExprK::Is(a, _, _) | ExprK::As(a, _, _) => calls_expr(a, out),
        ExprK::Binary(_, a, b) => {
            calls_expr(a, out);
            calls_expr(b, out);
        }
        ExprK::IfE(c, a, b) => {
            calls_expr(c, out);
            calls_expr(a, out);
            calls_expr(b, out);
        }
        ExprK::Quant { range, body, .. } => {
            if let Some((lo, hi)) = range {
                calls_expr(lo, out);
                calls_expr(hi, out);
            }
            calls_expr(body, out);
        }
        ExprK::Borrow { range: Some((lo, hi)), .. } => {
            calls_expr(lo, out);
            calls_expr(hi, out);
        }
        ExprK::Lit { fields, .. } => fields.iter().for_each(|(_, v)| calls_expr(v, out)),
        _ => {}
    }
}

fn calls_block(b: &Block, out: &mut Vec<String>) {
    for s in b {
        match &s.k {
            StmtK::Let { init: e, .. } | StmtK::Assign { val: e, .. } | StmtK::Assert(e) | StmtK::Expr(e) | StmtK::Return(Some(e)) => calls_expr(e, out),
            StmtK::Store { idx, val, .. } => {
                calls_expr(idx, out);
                calls_expr(val, out);
            }
            StmtK::If { cond, then, els } => {
                calls_expr(cond, out);
                calls_block(then, out);
                if let Some(e) = els {
                    calls_block(e, out);
                }
            }
            StmtK::While { cond, invs, dec, body } => {
                calls_expr(cond, out);
                invs.iter().for_each(|i| calls_expr(i, out));
                calls_expr(dec, out);
                calls_block(body, out);
            }
            StmtK::Par(bs) => bs.iter().for_each(|b| calls_expr(&b.call, out)),
            StmtK::Match { scrut, arms, .. } => {
                calls_expr(scrut, out);
                arms.iter().for_each(|a| calls_block(&a.body, out));
            }
            StmtK::Return(None) => {}
            StmtK::ParFor { lo, hi, ens, body, .. } => {
                calls_expr(lo, out);
                calls_expr(hi, out);
                ens.iter().for_each(|e| calls_expr(e, out));
                calls_block(body, out);
            }
        }
    }
}

/// The spec fns whose definitions a proof about `f` can depend on: those
/// named in `f` itself, in the contracts of anything it calls, and in the
/// bodies of those spec fns, transitively. Only these axioms go into `f`'s
/// solver query, so a definition elsewhere in the file cannot change
/// whether `f` proves. Leaving axioms out only weakens assumptions.
fn spec_deps(map: &HashMap<String, &Func>, lifted: &[Func], f: &Func) -> std::collections::HashSet<String> {
    let mut seen = std::collections::HashSet::new();
    let mut specs = std::collections::HashSet::new();
    let mut work = vec![];
    f.requires.iter().chain(&f.ensures).chain(&f.decreases).for_each(|e| calls_expr(e, &mut work));
    calls_block(&f.body, &mut work);
    while let Some(name) = work.pop() {
        if !seen.insert(name.clone()) {
            continue;
        }
        let Some(g) = map.get(&name) else { continue };
        g.requires.iter().chain(&g.ensures).chain(&g.decreases).for_each(|e| calls_expr(e, &mut work));
        if g.kind == FnKind::Spec {
            specs.insert(name);
            calls_block(&g.body, &mut work);
        } else if let Some(l) = lifted.iter().find(|l| l.name == name) {
            calls_block(&l.body, &mut work);
            specs.insert(name);
        }
    }
    specs
}

/// SMT declarations shared by every function: datatypes for structs and
/// enums, and spec fns with their definitional axioms. With `only`, axioms
/// are limited to those spec fns (every spec fn is still declared).
fn shared_prelude(prog: &Program, map: &HashMap<String, &Func>, lifted: &[Func], axioms: bool, only: Option<&std::collections::HashSet<String>>) -> String {
    let mut s = String::from(PRELUDE);
    if USES_BITS.load(Ordering::Relaxed) {
        s += BITS_DECLS;
    }
    if uses_count() {
        s += COUNT_DECLS;
        // Without axioms (spec fn checking, and the retry pass), count is an
        // uninterpreted function: weaker, never unsound.
        if axioms {
            s += COUNT_THEORY;
        }
    }
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
    let specs: Vec<&Func> = prog.funcs.iter().filter(|f| f.kind == FnKind::Spec).chain(lifted).collect();
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
    let specs: Vec<&Func> = if axioms { specs.into_iter().filter(|f| only.map_or(true, |o| o.contains(&f.name))).collect() } else { vec![] };
    for f in &specs {
        // An axiom body sits under the axiom's own quantifier.
        let mut g = Gen { prog, funcs: map, f, decls: vec![], obls: vec![], n: 0, dec_entry: None, par_borrows: None, ghost: true, wf: false, entry: HashMap::new(), quant: 1, arr_elem: IntK::I64, rec: None, rec_ens: false, in_old: 0 };
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
    let mut g = Gen { prog, funcs: map, f, decls: vec![], obls: vec![], n: 0, dec_entry: None, par_borrows: None, ghost: f.kind == FnKind::Lemma, wf: f.kind == FnKind::Spec, entry: HashMap::new(), quant: 0, arr_elem: IntK::I64, rec: None, rec_ens: false, in_old: 0 };
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
    g.entry = st.vars.clone();
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
        // The solver driver replaces this marker with a deterministic
        // resource budget for the check that follows (see run_z3).
        // Reachability needs a model, which quantified axioms make
        // expensive, so it gets a smaller budget and inconclusive results
        // are reported rather than failed.
        script += &format!("(echo \"@{}\")\n{}\n(check-sat)\n", i, if o.reach { BUDGET_REACH } else { BUDGET_PROOF });
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

const BUDGET_PROOF: &str = ";;keel-budget proof";
const BUDGET_REACH: &str = ";;keel-budget reach";

/// Solver budgets in Z3 resource units (`rlimit`). Unlike wall-clock
/// timeouts these count deterministic solver work, so the same program
/// gets the same verdict on every run and every machine load.
/// Calibrated against the examples and eval references, whose hardest
/// proof uses about 64M units (roughly 12 s); 200M leaves 3x headroom
/// while a runaway proof still fails in well under a minute.
const RLIMIT_PROOF: u64 = 200_000_000;
// Reachability: a path that is possible is confirmed almost at once, and a
// dead one is usually refuted just as fast; what remains is model search on
// quantified facts that rarely finishes. 200K matches 2M on every example
// and eval reference (same V-DEAD verdicts, same inconclusive counts).
const RLIMIT_REACH: u64 = 200_000;
const RLIMIT_RETRY: u64 = 10_000_000;

fn budget(var: &str, default: u64) -> u64 {
    std::env::var(var).ok().and_then(|v| v.parse().ok()).unwrap_or(default)
}

fn run_z3(script: &str) -> Result<String, String> {
    run_z3_budget(script, budget("KEEL_RLIMIT", RLIMIT_PROOF), budget("KEEL_RLIMIT_REACH", RLIMIT_REACH))
}

/// Drive one Z3 process interactively. Z3's `rlimit` counter is cumulative
/// over the whole process, so before each check we read the counter and
/// grant that check a fixed budget on top of it. A generous wall-clock
/// limit stays as a backstop against a hung solver; it is never meant to
/// decide a verdict.
fn run_z3_budget(script: &str, proof: u64, reach: u64) -> Result<String, String> {
    use std::io::{BufRead, BufReader};
    let mut child = Command::new(z3_path())
        .args(["-in", "-smt2", "-t:120000"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .map_err(|e| format!("could not run z3 ({}); install it or set KEEL_Z3", e))?;
    let mut stdin = child.stdin.take().unwrap();
    let mut lines = BufReader::new(child.stdout.take().unwrap()).lines();
    let log = std::env::var("KEEL_RLIMIT_LOG").is_ok();
    let mut out = String::new();
    let mut chunk = String::new();
    let mut last_count: Option<u64> = None;
    // Send `text`, then ask for the counter; collect output until it arrives.
    let mut send = |text: &str, out: &mut String| -> Result<u64, String> {
        stdin.write_all(text.as_bytes()).map_err(|e| e.to_string())?;
        stdin.write_all(b"(get-info :rlimit)\n").map_err(|e| e.to_string())?;
        stdin.flush().map_err(|e| e.to_string())?;
        loop {
            let line = match lines.next() {
                Some(l) => l.map_err(|e| e.to_string())?,
                None => return Err("z3 exited unexpectedly".into()),
            };
            if let Some(n) = line.trim().strip_prefix("(:rlimit ").and_then(|x| x.strip_suffix(')')) {
                return n.trim().parse().map_err(|_| format!("bad rlimit reply: {}", line));
            }
            out.push_str(&line);
            out.push('\n');
        }
    };
    for line in script.lines() {
        let kind = match line {
            BUDGET_PROOF => Some(proof),
            BUDGET_REACH => Some(reach),
            _ => None,
        };
        match kind {
            Some(b) => {
                let now = send(&chunk, &mut out)?;
                if log {
                    if let Some(prev) = last_count {
                        eprintln!("rlimit used: {}", now - prev);
                    }
                }
                last_count = Some(now);
                chunk = format!("(set-option :rlimit {})\n", now + b);
            }
            None => {
                chunk.push_str(line);
                chunk.push('\n');
            }
        }
    }
    let now = send(&chunk, &mut out)?;
    if log {
        if let Some(prev) = last_count {
            eprintln!("rlimit used: {}", now - prev);
        }
    }
    drop(send);
    let _ = child.kill();
    let _ = child.wait();
    Ok(out)
}

pub fn verify(prog: &Program, dump_dir: Option<&str>) -> Result<VResult, String> {
    let funcs = &prog.funcs;
    let dbg = format!("{:?}", funcs);
    USES_COUNT.store(dbg.contains("Call(\"count\""), Ordering::Relaxed);
    USES_BITS.store(["BitAnd", "BitOr", "BitXor", "BitNot", "Shl", "Shr"].iter().any(|k| dbg.contains(k)), Ordering::Relaxed);
    let map: HashMap<String, &Func> = funcs.iter().map(|f| (f.name.clone(), f)).collect();
    // Pure, loop-free fns as definitions, for specifications that call them.
    let lifted: Vec<Func> = funcs.iter().filter(|f| f.kind == FnKind::Code && crate::lift::why_not(&map, &f.name).is_none()).map(crate::lift::as_spec).collect();
    // Phase 1: spec fn definitions (no axioms). Phase 2: everything else,
    // only once every definition is known to be well-founded.
    let (specs, rest): (Vec<&Func>, Vec<&Func>) = funcs.iter().partition(|f| f.kind == FnKind::Spec);
    let mut total = VResult { diags: vec![], proved: 0, inconclusive: 0 };
    for (phase, axioms) in [(specs, false), (rest, true)] {
        let bare = shared_prelude(prog, &map, &lifted, false, None);
        let r = run_phase(prog, &map, &lifted, &phase, axioms, &bare, dump_dir)?;
        total.proved += r.proved;
        total.inconclusive += r.inconclusive;
        total.diags.extend(r.diags);
        if !total.diags.is_empty() {
            break;
        }
    }
    Ok(total)
}

/// Find a quantifier whose body indexes one array both at the bound
/// variable and at the bound variable shifted by a constant, as in
/// `forall t in 0..n { xs[t] < xs[t + 1] }`. Each instance creates the
/// term that triggers the next, a classic solver matching loop.
fn self_triggering_quantifier(f: &Func) -> Option<(Span, String, String)> {
    fn shifted(idx: &Expr, var: &str) -> bool {
        match &idx.k {
            ExprK::Binary(BOp::Add | BOp::Sub, a, b) => {
                matches!((&a.k, &b.k), (ExprK::Var(v), ExprK::Int(c)) if v == var && *c != 0)
                    || matches!((&a.k, &b.k), (ExprK::Int(c), ExprK::Var(v)) if v == var && *c != 0)
            }
            _ => false,
        }
    }
    fn indexes(e: &Expr, out: &mut Vec<(String, Expr)>) {
        match &e.k {
            ExprK::Index(a, i) => {
                out.push((a.clone(), (**i).clone()));
                indexes(i, out);
            }
            ExprK::Unary(_, a) | ExprK::Field(a, _) | ExprK::Is(a, _, _) | ExprK::As(a, _, _) | ExprK::Old(a) => indexes(a, out),
            ExprK::Binary(_, a, b) => {
                indexes(a, out);
                indexes(b, out);
            }
            ExprK::IfE(c, a, b) => {
                indexes(c, out);
                indexes(a, out);
                indexes(b, out);
            }
            ExprK::Quant { body, .. } => indexes(body, out),
            ExprK::Call(_, args) => args.iter().for_each(|x| indexes(x, out)),
            _ => {}
        }
    }
    fn find(e: &Expr) -> Option<(Span, String, String)> {
        match &e.k {
            ExprK::Quant { var, body, .. } => {
                let mut ix = vec![];
                indexes(body, &mut ix);
                for (arr, i) in &ix {
                    if matches!(&i.k, ExprK::Var(v) if v == var) && ix.iter().any(|(a2, j)| a2 == arr && shifted(j, var)) {
                        return Some((e.span, arr.clone(), var.clone()));
                    }
                }
                find(body)
            }
            ExprK::Unary(_, a) | ExprK::Old(a) => find(a),
            ExprK::Binary(_, a, b) => find(a).or_else(|| find(b)),
            ExprK::IfE(c, a, b) => find(c).or_else(|| find(a)).or_else(|| find(b)),
            _ => None,
        }
    }
    fn block(b: &Block) -> Option<(Span, String, String)> {
        for s in b {
            let r = match &s.k {
                StmtK::While { invs, body, .. } => invs.iter().find_map(find).or_else(|| block(body)),
                StmtK::If { then, els, .. } => block(then).or_else(|| els.as_ref().and_then(block)),
                StmtK::Match { arms, .. } => arms.iter().find_map(|a| block(&a.body)),
                StmtK::Assert(e) => find(e),
                StmtK::ParFor { ens, body, .. } => ens.iter().find_map(find).or_else(|| block(body)),
                _ => None,
            };
            if r.is_some() {
                return r;
            }
        }
        None
    }
    f.requires.iter().chain(&f.ensures).find_map(find).or_else(|| block(&f.body))
}

fn loop_hint(looping: &Option<(Span, String, String)>) -> Option<String> {
    looping.as_ref().map(|(span, arr, var)| {
        format!(
            "the quantifier at line {}:{} reads {}[{}] and a shifted index such as {}[{} + 1], which can make the solver instantiate it forever. State it pairwise instead, for example forall a in lo..hi {{ forall b in a..hi {{ {}[a] <= {}[b] }} }}",
            span.line, span.col, arr, var, arr, var, arr, arr
        )
    })
}

fn run_phase(prog: &Program, map: &HashMap<String, &Func>, lifted: &[Func], funcs: &[&Func], axioms: bool, bare: &str, dump_dir: Option<&str>) -> Result<VResult, String> {
    let jobs: Vec<(Vec<String>, Vec<Obl>)> = funcs.iter().map(|f| gen_func(prog, map, f)).collect();
    let scripts: Vec<String> = jobs
        .iter()
        .zip(funcs)
        .map(|((d, o), f)| {
            let prelude = if axioms { shared_prelude(prog, map, lifted, true, Some(&spec_deps(map, lifted, f))) } else { bare.to_string() };
            build_script(&prelude, d, o, &(0..o.len()).collect::<Vec<_>>(), false)
        })
        .collect();
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
                        run_z3_budget(&build_script(bare, d, o, pick, true), budget("KEEL_RLIMIT_RETRY", RLIMIT_RETRY), budget("KEEL_RLIMIT_REACH", RLIMIT_REACH)).map(|out| (parse_results(&out), solver_error(&out))).unwrap_or_default()
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
    for ((((_, obls), res1), res2), f) in jobs.iter().zip(&first).zip(&second).zip(funcs) {
        let looping = self_triggering_quantifier(f);
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
                        let hint = loop_hint(&looping).unwrap_or_else(|| o.hint.to_string());
                        let mut d = Diag::new(o.code, o.span, format!("{} (the solver ran out of budget; this counterexample ignores quantified facts and may be spurious)", o.msg)).hint(hint);
                        d.cex = model_values(&m, &o.cex);
                        diags.push(d);
                    }
                    _ => {
                        let why = if other.starts_with("(error") { format!("solver error: {}", other) } else { "solver ran out of budget".into() };
                        let hint = loop_hint(&looping).unwrap_or_else(|| o.hint.to_string());
                        diags.push(Diag::new("V-UNKNOWN", o.span, format!("could not prove: {} ({})", o.msg, why)).hint(hint));
                    }
                },
            }
        }
    }
    diags.sort_by_key(|d| (d.span.line, d.span.col));
    Ok(VResult { diags, proved, inconclusive })
}
