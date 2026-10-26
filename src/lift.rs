// Lifting: lets specifications call a pure, loop-free `fn` directly.
//
// Such a function's body is rewritten into one expression (lets become
// substitutions, ifs become if-expressions) and given to the solver as a
// definition, exactly like a spec fn. This is sound because the function
// is verified like any other: under its requires the body never overflows,
// divides by zero or reads out of bounds, so its mathematical reading
// equals what the code computes. Lifting is non-recursive by construction,
// so every definition is well-founded.

use crate::ast::*;
use std::collections::HashMap;

/// Why `name` cannot be called from a specification, or None if it can.
pub fn why_not(funcs: &HashMap<String, &Func>, name: &str) -> Option<String> {
    why_not_in(funcs, name, &mut vec![]).map(|w| format!("'{}' {}", name, w))
}

fn why_not_in(funcs: &HashMap<String, &Func>, name: &str, stack: &mut Vec<String>) -> Option<String> {
    let f = funcs.get(name)?;
    if f.kind != FnKind::Code {
        return None;
    }
    if stack.iter().any(|s| s == name) {
        return Some("is recursive".into());
    }
    if f.io {
        return Some("is io".into());
    }
    if !matches!(f.ret, Ty::I64 | Ty::Bool | Ty::Named(_)) {
        return Some("does not return i64, bool or a struct/enum".into());
    }
    if let Some(p) = f.params.iter().find(|p| !matches!(p.ty, Ty::I64 | Ty::Bool | Ty::Named(_) | Ty::Ref)) {
        return Some(format!("takes '{}' as {}, which may be mutated", p.name, p.ty.name()));
    }
    stack.push(name.to_string());
    let r = block_why(funcs, &f.body, stack);
    stack.pop();
    r
}

fn block_why(funcs: &HashMap<String, &Func>, b: &Block, stack: &mut Vec<String>) -> Option<String> {
    for s in b {
        let r = match &s.k {
            StmtK::Let { init: e, ty, .. } => {
                if ty.is_array() {
                    Some("creates an array".to_string())
                } else {
                    expr_why(funcs, e, stack)
                }
            }
            StmtK::Assign { path, val, .. } => {
                if path.is_empty() {
                    expr_why(funcs, val, stack)
                } else {
                    Some("assigns a field".to_string())
                }
            }
            StmtK::Return(Some(e)) => expr_why(funcs, e, stack),
            StmtK::If { cond, then, els } => expr_why(funcs, cond, stack).or_else(|| block_why(funcs, then, stack)).or_else(|| els.as_ref().and_then(|e| block_why(funcs, e, stack))),
            // Asserts were proven and lemma calls are ghost: both are erased.
            StmtK::Assert(_) => None,
            StmtK::Expr(Expr { k: ExprK::Call(n, _), .. }) if funcs.get(n).is_some_and(|g| g.kind == FnKind::Lemma) => None,
            StmtK::While { .. } => Some("contains a loop".to_string()),
            StmtK::Store { .. } => Some("writes to an array".to_string()),
            StmtK::Par(_) => Some("runs par branches".to_string()),
            StmtK::Match { .. } => Some("contains a match statement".to_string()),
            StmtK::Expr(_) | StmtK::Return(None) => Some("calls a function for its effect".to_string()),
        };
        if r.is_some() {
            return r;
        }
    }
    None
}

fn expr_why(funcs: &HashMap<String, &Func>, e: &Expr, stack: &mut Vec<String>) -> Option<String> {
    match &e.k {
        ExprK::Call(n, args) => {
            if matches!(n.as_str(), "array" | "print") {
                return Some(format!("calls {}", n));
            }
            if stack.iter().any(|s| s == n) {
                return Some(format!("is recursive (calls '{}')", n));
            }
            if let Some(w) = why_not_in(funcs, n, stack) {
                return Some(format!("calls '{}', which {}", n, w));
            }
            args.iter().find_map(|a| expr_why(funcs, a, stack))
        }
        ExprK::Index(_, a) | ExprK::Unary(_, a) | ExprK::Field(a, _) | ExprK::Is(a, _, _) | ExprK::As(a, _, _) | ExprK::Old(a) => expr_why(funcs, a, stack),
        ExprK::Binary(_, a, b) => expr_why(funcs, a, stack).or_else(|| expr_why(funcs, b, stack)),
        ExprK::IfE(c, a, b) => expr_why(funcs, c, stack).or_else(|| expr_why(funcs, a, stack)).or_else(|| expr_why(funcs, b, stack)),
        ExprK::Borrow { range: Some((lo, hi)), .. } => expr_why(funcs, lo, stack).or_else(|| expr_why(funcs, hi, stack)),
        ExprK::Lit { fields, .. } => fields.iter().find_map(|(_, v)| expr_why(funcs, v, stack)),
        _ => None,
    }
}

/// A liftable function as a spec fn: same signature and requires, its body
/// rewritten into a single expression. Call only when `why_not` is None.
pub fn as_spec(f: &Func) -> Func {
    let body = lift(&f.body, &HashMap::new()).expect("liftable bodies always return");
    let span = f.span;
    Func { kind: FnKind::Spec, ensures: vec![], decreases: None, body: vec![Stmt { k: StmtK::Return(Some(body)), span }], ..f.clone() }
}

/// The value `b` returns, with local variables replaced by their values.
/// Keel forbids shadowing, so a name means the same variable everywhere it
/// is in scope, and appending the rest of a block to an `if` branch is safe.
fn lift(b: &[Stmt], env: &HashMap<String, Expr>) -> Option<Expr> {
    let (s, rest) = b.split_first()?;
    match &s.k {
        StmtK::Let { name, init: e, .. } | StmtK::Assign { name, val: e, .. } => {
            let mut env = env.clone();
            env.insert(name.clone(), subst(e, &env));
            lift(rest, &env)
        }
        StmtK::Return(Some(e)) => Some(subst(e, env)),
        StmtK::If { cond, then, els } => {
            let c = subst(cond, env);
            let t: Vec<Stmt> = then.iter().chain(rest).cloned().collect();
            let e: Vec<Stmt> = els.iter().flatten().chain(rest).cloned().collect();
            Some(Expr { k: ExprK::IfE(Box::new(c), Box::new(lift(&t, env)?), Box::new(lift(&e, env)?)), span: s.span })
        }
        _ => lift(rest, env),
    }
}

fn subst(e: &Expr, env: &HashMap<String, Expr>) -> Expr {
    let b = |x: &Expr| Box::new(subst(x, env));
    let k = match &e.k {
        ExprK::Var(n) => return env.get(n).cloned().unwrap_or_else(|| e.clone()),
        ExprK::Call(n, args) => ExprK::Call(n.clone(), args.iter().map(|a| subst(a, env)).collect()),
        ExprK::Index(n, i) => ExprK::Index(n.clone(), b(i)),
        ExprK::Unary(op, a) => ExprK::Unary(*op, b(a)),
        ExprK::Binary(op, x, y) => ExprK::Binary(*op, b(x), b(y)),
        ExprK::Borrow { name, mutable, range } => ExprK::Borrow { name: name.clone(), mutable: *mutable, range: range.as_ref().map(|(lo, hi)| (b(lo), b(hi))) },
        ExprK::Lit { ty, variant, fields } => ExprK::Lit { ty: *ty, variant: variant.clone(), fields: fields.iter().map(|(n, v)| (n.clone(), subst(v, env))).collect() },
        ExprK::Field(a, n) => ExprK::Field(b(a), n.clone()),
        ExprK::Is(a, t, v) => ExprK::Is(b(a), *t, v.clone()),
        ExprK::As(a, t, v) => ExprK::As(b(a), *t, v.clone()),
        ExprK::IfE(c, x, y) => ExprK::IfE(b(c), b(x), b(y)),
        ExprK::Old(a) => ExprK::Old(b(a)),
        ExprK::Quant { .. } | ExprK::Int(_) | ExprK::Bool(_) | ExprK::Result => return e.clone(),
    };
    Expr { k, span: e.span }
}
