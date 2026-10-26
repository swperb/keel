// GPU backend: each eligible `par for` body becomes a PTX kernel, one
// thread per iteration. PTX is NVIDIA's virtual ISA; the driver compiles it
// for whatever GPU is present when the program loads it, so building needs
// no CUDA toolkit and the generated C needs only the driver at run time.
//
// The verifier already proved every iteration independent (V-RACE) and
// every operation in range, so, as in the C backend, nothing is checked at
// run time. Values are computed in 64-bit registers, exactly like Keel's i64
// arithmetic; narrow array elements are sign- or zero-extended on load and
// truncated on store, which the verifier proved lossless.
//
// A body the GPU cannot run (struct or enum values) is not an error: the
// loop stays on the CPU, and `keel build` says why.

use crate::ast::*;
use std::collections::{BTreeSet, HashMap};

/// A compiled kernel: its PTX entry, the callees it needs, and the outer
/// variables it takes, in parameter order.
pub struct Kernel {
    pub name: String,
    pub entry: String,
    pub callees: BTreeSet<String>,
    /// Outer scalars: f32 as itself, everything else as a 64-bit value.
    pub scalars: Vec<(String, Ty)>,
    /// Outer arrays: (name, element type, written by the loop).
    pub arrays: Vec<(String, IntK, bool)>,
}

struct Arr {
    ptr: String,
    len: String,
    elem: IntK,
}

struct Px<'a> {
    funcs: &'a HashMap<&'a str, &'a Func>,
    out: String,
    rd: usize,
    r: usize,
    f: usize,
    p: usize,
    label: usize,
    vals: HashMap<String, String>,
    arrs: HashMap<String, Arr>,
    callees: BTreeSet<String>,
}

type R<T> = Result<T, String>;

fn bytes(k: IntK) -> u32 {
    k.bits() / 8
}

fn mem_ty(k: IntK) -> &'static str {
    match k {
        IntK::I8 => "s8",
        IntK::I16 => "s16",
        IntK::I32 => "s32",
        IntK::I64 => "s64",
        IntK::U8 => "u8",
        IntK::U16 => "u16",
        IntK::U32 => "u32",
        IntK::F32 => "f32",
    }
}

/// f32 values live in `%f` registers, everything else in 64-bit `%rd`.
fn is_f(reg: &str) -> bool {
    reg.starts_with("%f")
}

/// PTX parameter type for a scalar.
fn pty(t: Ty) -> &'static str {
    if t == Ty::F32 {
        "f32"
    } else {
        "b64"
    }
}

/// A scalar type the GPU path can carry in a 64-bit register.
fn scalar_ok(t: Ty) -> bool {
    matches!(t, Ty::Int(_) | Ty::Bool | Ty::F32)
}

impl<'a> Px<'a> {
    fn new(funcs: &'a HashMap<&'a str, &'a Func>) -> Px<'a> {
        Px { funcs, out: String::new(), rd: 0, r: 0, f: 0, p: 0, label: 0, vals: HashMap::new(), arrs: HashMap::new(), callees: BTreeSet::new() }
    }
    fn i(&mut self, s: &str) {
        self.out += "\t";
        self.out += s;
        self.out += "\n";
    }
    fn rd(&mut self) -> String {
        self.rd += 1;
        format!("%rd{}", self.rd)
    }
    fn r32(&mut self) -> String {
        self.r += 1;
        format!("%r{}", self.r)
    }
    fn freg(&mut self) -> String {
        self.f += 1;
        format!("%f{}", self.f)
    }
    /// A fresh register of `v`'s kind.
    fn like(&mut self, v: &str) -> String {
        if is_f(v) {
            self.freg()
        } else {
            self.rd()
        }
    }
    fn mov(v: &str) -> &'static str {
        if is_f(v) {
            "mov.f32"
        } else {
            "mov.b64"
        }
    }
    fn pred(&mut self) -> String {
        self.p += 1;
        format!("%p{}", self.p)
    }
    fn label(&mut self) -> String {
        self.label += 1;
        format!("$L{}", self.label)
    }
    fn regs(&self) -> String {
        format!("\t.reg .b64 %rd<{}>;\n\t.reg .b32 %r<{}>;\n\t.reg .f32 %f<{}>;\n\t.reg .pred %p<{}>;\n", self.rd + 1, self.r + 1, self.f + 1, self.p + 1)
    }

    /// Address of xs[idx].
    fn addr(&mut self, name: &str, idx: &str) -> (String, IntK) {
        let a = &self.arrs[name];
        let (ptr, elem) = (a.ptr.clone(), a.elem);
        let d = self.rd();
        self.i(&format!("mad.lo.s64 {}, {}, {}, {};", d, idx, bytes(elem), ptr));
        (d, elem)
    }

    fn ex(&mut self, e: &Expr) -> R<String> {
        Ok(match &e.k {
            ExprK::Int(v) => {
                let d = self.rd();
                let lit = if *v == i64::MIN as i128 { "0x8000000000000000".to_string() } else { v.to_string() };
                self.i(&format!("mov.b64 {}, {};", d, lit));
                d
            }
            ExprK::Float(v) => {
                // Exact: PTX takes an f32 literal as its IEEE bits.
                let d = self.freg();
                self.i(&format!("mov.f32 {}, 0f{:08X};", d, v.to_bits()));
                d
            }
            ExprK::Bool(b) => {
                let d = self.rd();
                self.i(&format!("mov.b64 {}, {};", d, *b as i32));
                d
            }
            ExprK::Var(n) => self.vals.get(n).cloned().ok_or_else(|| format!("uses '{}', which the GPU path cannot carry", n))?,
            ExprK::Index(n, idx) => {
                let iv = self.ex(idx)?;
                let (a, k) = self.addr(n, &iv);
                if k == IntK::F32 {
                    let d = self.freg();
                    self.i(&format!("ld.global.f32 {}, [{}];", d, a));
                    return Ok(d);
                }
                let d = self.rd();
                if k == IntK::I64 {
                    self.i(&format!("ld.global.s64 {}, [{}];", d, a));
                } else {
                    let r = self.r32();
                    self.i(&format!("ld.global.{} {}, [{}];", mem_ty(k), r, a));
                    self.i(&format!("cvt.{}64.{}32 {}, {};", if k.signed() { "s" } else { "u" }, if k.signed() { "s" } else { "u" }, d, r));
                }
                d
            }
            ExprK::Unary(op, a) => {
                let av = self.ex(a)?;
                if is_f(&av) {
                    let d = self.freg();
                    self.i(&format!("neg.f32 {}, {};", d, av));
                    return Ok(d);
                }
                let d = self.rd();
                match op {
                    UOp::Neg => self.i(&format!("neg.s64 {}, {};", d, av)),
                    UOp::Not => self.i(&format!("xor.b64 {}, {}, 1;", d, av)),
                    UOp::BitNot => self.i(&format!("not.b64 {}, {};", d, av)),
                }
                d
            }
            ExprK::Binary(op @ (BOp::And | BOp::Or | BOp::Implies), a, b) => {
                // Short-circuit, as in C: the right side may only be safe
                // to evaluate when the left side allows it.
                let av = self.ex(a)?;
                let d = self.rd();
                let p = self.pred();
                let skip = self.label();
                match op {
                    BOp::And => {
                        self.i(&format!("mov.b64 {}, {};", d, av));
                        self.i(&format!("setp.eq.s64 {}, {}, 0;", p, av));
                    }
                    BOp::Or => {
                        self.i(&format!("mov.b64 {}, {};", d, av));
                        self.i(&format!("setp.ne.s64 {}, {}, 0;", p, av));
                    }
                    _ => {
                        self.i(&format!("xor.b64 {}, {}, 1;", d, av));
                        self.i(&format!("setp.ne.s64 {}, {}, 0;", p, d));
                    }
                }
                self.i(&format!("@{} bra {};", p, skip));
                let bv = self.ex(b)?;
                self.i(&format!("mov.b64 {}, {};", d, bv));
                self.out += &format!("{}:\n", skip);
                d
            }
            ExprK::Binary(op, a, b) => {
                let av = self.ex(a)?;
                let bv = self.ex(b)?;
                if is_f(&av) {
                    // IEEE, round to nearest; explicit .rn also forbids
                    // fusing a * b + c into one fma, matching the C build.
                    let ins = match op {
                        BOp::Add => "add.rn.f32",
                        BOp::Sub => "sub.rn.f32",
                        BOp::Mul => "mul.rn.f32",
                        BOp::Div => "div.rn.f32",
                        _ => "",
                    };
                    if !ins.is_empty() {
                        let d = self.freg();
                        self.i(&format!("{} {}, {}, {};", ins, d, av, bv));
                        return Ok(d);
                    }
                    // C's comparisons: false on NaN, except != (unordered).
                    let c = match op {
                        BOp::Eq => "eq",
                        BOp::Ne => "neu",
                        BOp::Lt => "lt",
                        BOp::Le => "le",
                        BOp::Gt => "gt",
                        _ => "ge",
                    };
                    let (p, d) = (self.pred(), self.rd());
                    self.i(&format!("setp.{}.f32 {}, {}, {};", c, p, av, bv));
                    self.i(&format!("selp.b64 {}, 1, 0, {};", d, p));
                    return Ok(d);
                }
                let d = self.rd();
                let cmp = match op {
                    BOp::Eq => Some("eq"),
                    BOp::Ne => Some("ne"),
                    BOp::Lt => Some("lt"),
                    BOp::Le => Some("le"),
                    BOp::Gt => Some("gt"),
                    BOp::Ge => Some("ge"),
                    _ => None,
                };
                if let Some(c) = cmp {
                    let p = self.pred();
                    self.i(&format!("setp.{}.s64 {}, {}, {};", c, p, av, bv));
                    self.i(&format!("selp.b64 {}, 1, 0, {};", d, p));
                    return Ok(d);
                }
                match op {
                    BOp::Shl | BOp::Shr => {
                        let r = self.r32();
                        self.i(&format!("cvt.u32.u64 {}, {};", r, bv));
                        let ins = if *op == BOp::Shl { "shl.b64" } else { "shr.s64" };
                        self.i(&format!("{} {}, {}, {};", ins, d, av, r));
                    }
                    _ => {
                        let ins = match op {
                            BOp::Add => "add.s64",
                            BOp::Sub => "sub.s64",
                            BOp::Mul => "mul.lo.s64",
                            BOp::Div => "div.s64",
                            BOp::Mod => "rem.s64",
                            BOp::BitAnd => "and.b64",
                            BOp::BitOr => "or.b64",
                            BOp::BitXor => "xor.b64",
                            _ => unreachable!(),
                        };
                        self.i(&format!("{} {}, {}, {};", ins, d, av, bv));
                    }
                }
                d
            }
            ExprK::Call(name, args) => self.call(name, args)?.ok_or("uses a unit call as a value")?,
            ExprK::Lit { .. } | ExprK::Field(..) | ExprK::Is(..) => return Err("uses struct or enum values".into()),
            ExprK::Result | ExprK::Quant { .. } | ExprK::Borrow { .. } | ExprK::IfE(..) | ExprK::As(..) | ExprK::Old(..) => unreachable!("specs are erased"),
        })
    }

    /// A call; Some(register) unless it returns unit.
    fn call(&mut self, name: &str, args: &[Expr]) -> R<Option<String>> {
        if name == "len" {
            let ExprK::Var(n) = &args[0].k else { unreachable!() };
            return Ok(Some(self.arrs[n.as_str()].len.clone()));
        }
        match name {
            "to_f32" => {
                let v = self.ex(&args[0])?;
                let d = self.freg();
                self.i(&format!("cvt.rn.f32.s64 {}, {};", d, v));
                return Ok(Some(d));
            }
            "to_i64" => {
                // Toward zero, saturating, NaN to 0, as klrt_f2i in C. PTX's
                // cvt saturates, but turns NaN into i64::MIN, so test it.
                let v = self.ex(&args[0])?;
                let (d, p) = (self.rd(), self.pred());
                self.i(&format!("cvt.rzi.s64.f32 {}, {};", d, v));
                self.i(&format!("setp.nan.f32 {}, {}, {};", p, v, v));
                self.i(&format!("selp.b64 {}, 0, {}, {};", d, d, p));
                return Ok(Some(d));
            }
            "f32_bits" => {
                let v = self.ex(&args[0])?;
                let (r, d) = (self.r32(), self.rd());
                self.i(&format!("mov.b32 {}, {};", r, v));
                self.i(&format!("cvt.u64.u32 {}, {};", d, r));
                return Ok(Some(d));
            }
            _ => {}
        }
        if let Some(k) = crate::check::wrap_kind(name) {
            // + - * wrap modulo 2^64 in PTX, which is exact modulo 2^N;
            // then reduce into the type's range.
            let v = self.ex(&args[0])?;
            if k == IntK::I64 {
                return Ok(Some(v));
            }
            let d = self.rd();
            if k.signed() {
                let s = 64 - k.bits();
                self.i(&format!("shl.b64 {}, {}, {};", d, v, s));
                self.i(&format!("shr.s64 {}, {}, {};", d, d, s));
            } else {
                self.i(&format!("and.b64 {}, {}, {};", d, v, (1u64 << k.bits()) - 1));
            }
            return Ok(Some(d));
        }
        let g = *self.funcs.get(name).ok_or_else(|| format!("calls '{}'", name))?;
        let mut vals = vec![];
        for (a, p) in args.iter().zip(&g.params) {
            if p.ty.is_array() {
                let ExprK::Borrow { name: an, range, .. } = &a.k else { unreachable!() };
                let (ptr, len, elem) = {
                    let x = &self.arrs[an.as_str()];
                    (x.ptr.clone(), x.len.clone(), x.elem)
                };
                match range {
                    None => {
                        vals.push(ptr);
                        vals.push(len);
                    }
                    Some((lo, hi)) => {
                        let lv = self.ex(lo)?;
                        let hv = self.ex(hi)?;
                        let (pp, ll) = (self.rd(), self.rd());
                        self.i(&format!("mad.lo.s64 {}, {}, {}, {};", pp, lv, bytes(elem), ptr));
                        self.i(&format!("sub.s64 {}, {}, {};", ll, hv, lv));
                        vals.push(pp);
                        vals.push(ll);
                    }
                }
            } else {
                vals.push(self.ex(a)?);
            }
        }
        self.callees.insert(name.to_string());
        let mut s = String::from("{\n");
        for (k, v) in vals.iter().enumerate() {
            let t = if is_f(v) { "f32" } else { "b64" };
            s += &format!("\t.param .{t} a{k};\n\tst.param.{t} [a{k}], {v};\n", t = t, k = k, v = v);
        }
        let plist = if vals.is_empty() { String::new() } else { format!(", ({})", (0..vals.len()).map(|k| format!("a{}", k)).collect::<Vec<_>>().join(", ")) };
        let ret = if g.ret == Ty::Unit {
            s += &format!("\tcall.uni kl_{}{};\n", name, plist);
            None
        } else {
            let t = pty(g.ret);
            let d = if g.ret == Ty::F32 { self.freg() } else { self.rd() };
            s += &format!("\t.param .{t} rv;\n\tcall.uni (rv), kl_{}{};\n\tld.param.{t} {}, [rv];\n", name, plist, d, t = t);
            Some(d)
        };
        s += "\t}\n";
        self.out += "\t";
        self.out += &s;
        Ok(ret)
    }

    fn block(&mut self, b: &Block) -> R<()> {
        for s in b {
            self.stmt(s)?;
        }
        Ok(())
    }

    fn stmt(&mut self, s: &Stmt) -> R<()> {
        match &s.k {
            StmtK::Let { name, ty, init, .. } => {
                if !scalar_ok(*ty) {
                    return Err(format!("declares '{}' of type {}", name, ty.name()));
                }
                let v = self.ex(init)?;
                let d = self.like(&v);
                self.i(&format!("{} {}, {};", Px::mov(&v), d, v));
                self.vals.insert(name.clone(), d);
            }
            StmtK::Assign { name, path, val } => {
                if !path.is_empty() {
                    return Err("assigns a struct field".into());
                }
                let v = self.ex(val)?;
                let d = self.vals[name.as_str()].clone();
                self.i(&format!("{} {}, {};", Px::mov(&v), d, v));
            }
            StmtK::Store { name, idx, val } => {
                let iv = self.ex(idx)?;
                let vv = self.ex(val)?;
                let (a, k) = self.addr(name, &iv);
                if k == IntK::F32 {
                    self.i(&format!("st.global.f32 [{}], {};", a, vv));
                } else if k == IntK::I64 {
                    self.i(&format!("st.global.s64 [{}], {};", a, vv));
                } else {
                    let r = self.r32();
                    self.i(&format!("cvt.u32.u64 {}, {};", r, vv));
                    self.i(&format!("st.global.{} [{}], {};", mem_ty(k), a, r));
                }
            }
            StmtK::If { cond, then, els } => {
                let c = self.ex(cond)?;
                let p = self.pred();
                let (l_else, l_end) = (self.label(), self.label());
                self.i(&format!("setp.eq.s64 {}, {}, 0;", p, c));
                self.i(&format!("@{} bra {};", p, l_else));
                self.block(then)?;
                self.i(&format!("bra.uni {};", l_end));
                self.out += &format!("{}:\n", l_else);
                if let Some(e) = els {
                    self.block(e)?;
                }
                self.out += &format!("{}:\n", l_end);
            }
            StmtK::While { cond, body, .. } => {
                let (l_top, l_end) = (self.label(), self.label());
                self.out += &format!("{}:\n", l_top);
                let c = self.ex(cond)?;
                let p = self.pred();
                self.i(&format!("setp.eq.s64 {}, {}, 0;", p, c));
                self.i(&format!("@{} bra {};", p, l_end));
                self.block(body)?;
                self.i(&format!("bra.uni {};", l_top));
                self.out += &format!("{}:\n", l_end);
            }
            StmtK::Return(e) => {
                if let Some(e) = e {
                    let v = self.ex(e)?;
                    self.i(&format!("st.param.{} [ret], {};", if is_f(&v) { "f32" } else { "b64" }, v));
                }
                self.i("ret;");
            }
            StmtK::Assert(_) => {}
            StmtK::Expr(e) => {
                if let ExprK::Call(n, args) = &e.k {
                    if self.funcs.get(n.as_str()).map(|f| f.kind) == Some(FnKind::Lemma) {
                        return Ok(());
                    }
                    self.call(n, args)?;
                }
            }
            StmtK::Match { .. } => return Err("contains a match statement".into()),
            StmtK::Par(_) | StmtK::ParFor { .. } => unreachable!("checked"),
        }
        Ok(())
    }
}

/// The PTX header of a `.func` for `f`: arrays are (pointer, length) pairs,
/// scalars one 64-bit value each.
fn func_header(f: &Func) -> R<String> {
    let mut ps = vec![];
    for p in &f.params {
        if p.ty.is_array() {
            ps.push(format!(".param .b64 p_{}", p.name));
            ps.push(format!(".param .b64 p_{}_len", p.name));
        } else if scalar_ok(p.ty) {
            ps.push(format!(".param .{} p_{}", pty(p.ty), p.name));
        } else {
            return Err(format!("calls '{}', which takes a {}", f.name, p.ty.name()));
        }
    }
    let ret = match f.ret {
        Ty::Unit => String::new(),
        t if scalar_ok(t) => format!("(.param .{} ret) ", pty(t)),
        t => return Err(format!("calls '{}', which returns a {}", f.name, t.name())),
    };
    let plist = if ps.is_empty() { String::new() } else { format!(" ({})", ps.join(", ")) };
    Ok(format!(".func {}kl_{}{}", ret, f.name, plist))
}

/// Compile a callee to a PTX `.func` definition; also returns its callees.
fn func(_prog: &Program, funcs: &HashMap<&str, &Func>, f: &Func) -> R<(String, BTreeSet<String>)> {
    let header = func_header(f)?;
    let mut px = Px::new(funcs);
    for p in &f.params {
        let d = if p.ty == Ty::F32 { px.freg() } else { px.rd() };
        px.i(&format!("ld.param.{} {}, [p_{}];", pty(p.ty), d, p.name));
        if let Some(elem) = p.ty.elem() {
            let l = px.rd();
            px.i(&format!("ld.param.b64 {}, [p_{}_len];", l, p.name));
            px.arrs.insert(p.name.clone(), Arr { ptr: d, len: l, elem });
        } else {
            px.vals.insert(p.name.clone(), d);
        }
    }
    px.block(&f.body).map_err(|w| format!("calls '{}', which {}", f.name, w))?;
    if f.ret == Ty::Unit {
        px.i("ret;");
    }
    Ok((format!("{}\n{{\n{}{}}}\n", header, px.regs(), px.out), px.callees))
}

/// Names used in `b` that it does not declare itself, in first-use order.
fn free_names(b: &Block, out: &mut Vec<String>, bound: &mut Vec<String>) {
    fn ex(e: &Expr, out: &mut Vec<String>, bound: &[String]) {
        let mut add = |n: &String| {
            if !bound.contains(n) && !out.contains(n) {
                out.push(n.clone());
            }
        };
        match &e.k {
            ExprK::Var(n) => add(n),
            ExprK::Index(n, i) => {
                add(n);
                ex(i, out, bound);
            }
            ExprK::Borrow { name, range, .. } => {
                add(name);
                if let Some((lo, hi)) = range {
                    ex(lo, out, bound);
                    ex(hi, out, bound);
                }
            }
            ExprK::Call(_, args) => args.iter().for_each(|a| ex(a, out, bound)),
            ExprK::Unary(_, a) | ExprK::Field(a, _) | ExprK::Is(a, _, _) => ex(a, out, bound),
            ExprK::Binary(_, a, b) => {
                ex(a, out, bound);
                ex(b, out, bound);
            }
            ExprK::Lit { fields, .. } => fields.iter().for_each(|(_, f)| ex(f, out, bound)),
            _ => {}
        }
    }
    for s in b {
        match &s.k {
            StmtK::Let { name, init, .. } => {
                ex(init, out, bound);
                bound.push(name.clone());
            }
            StmtK::Assign { name, val, .. } => {
                ex(val, out, bound);
                if !bound.contains(name) && !out.contains(name) {
                    out.push(name.clone());
                }
            }
            StmtK::Store { name, idx, val } => {
                if !bound.contains(name) && !out.contains(name) {
                    out.push(name.clone());
                }
                ex(idx, out, bound);
                ex(val, out, bound);
            }
            StmtK::If { cond, then, els } => {
                ex(cond, out, bound);
                free_names(then, out, bound);
                if let Some(e) = els {
                    free_names(e, out, bound);
                }
            }
            StmtK::While { cond, body, .. } => {
                ex(cond, out, bound);
                free_names(body, out, bound);
            }
            StmtK::Match { scrut, arms, .. } => {
                ex(scrut, out, bound);
                for a in arms {
                    if let Some(b) = &a.binder {
                        bound.push(b.clone());
                    }
                    free_names(&a.body, out, bound);
                }
            }
            StmtK::Return(Some(e)) | StmtK::Expr(e) => ex(e, out, bound),
            _ => {}
        }
    }
}

/// Compile a `par for` body to a kernel entry, or say why it stays on the CPU.
/// `outer` gives the types of the variables in scope around the loop.
pub fn kernel(prog: &Program, funcs: &HashMap<&str, &Func>, id: usize, var: &str, body: &Block, outer: &HashMap<String, Ty>) -> R<Kernel> {
    let mut names = vec![];
    free_names(body, &mut names, &mut vec![var.to_string()]);
    let mut written = std::collections::HashSet::new();
    crate::verify::mods_of(body, &mut written);
    let name = format!("kl_k{}", id);
    let mut px = Px::new(funcs);
    let mut params = vec![".param .b64 k_lo".to_string(), ".param .b64 k_n".to_string()];
    let (mut scalars, mut arrays) = (vec![], vec![]);
    let t = px.rd();
    let (c, nt, tid) = (px.r32(), px.r32(), px.r32());
    px.i(&format!("mov.u32 {}, %ctaid.x;", c));
    px.i(&format!("mov.u32 {}, %ntid.x;", nt));
    px.i(&format!("mov.u32 {}, %tid.x;", tid));
    px.i(&format!("mul.wide.u32 {}, {}, {};", t, c, nt));
    let t2 = px.rd();
    px.i(&format!("cvt.u64.u32 {}, {};", t2, tid));
    px.i(&format!("add.s64 {}, {}, {};", t, t, t2));
    let n = px.rd();
    px.i(&format!("ld.param.b64 {}, [k_n];", n));
    let p = px.pred();
    px.i(&format!("setp.ge.u64 {}, {}, {};", p, t, n));
    px.i(&format!("@{} bra $Lexit;", p));
    let lo = px.rd();
    px.i(&format!("ld.param.b64 {}, [k_lo];", lo));
    let iv = px.rd();
    px.i(&format!("add.s64 {}, {}, {};", iv, lo, t));
    px.vals.insert(var.to_string(), iv);
    // Scalars first, then arrays: the order the host launcher passes them.
    let mut names: Vec<(String, Ty)> = names.into_iter().filter_map(|n| outer.get(&n).map(|t| (n, *t))).collect();
    names.sort_by_key(|(_, t)| t.is_array());
    for (n, ty) in &names {
        if let Some(elem) = ty.elem() {
            let (d, l) = (px.rd(), px.rd());
            px.i(&format!("ld.param.b64 {}, [k_{}];", d, n));
            px.i(&format!("cvta.to.global.u64 {}, {};", d, d));
            px.i(&format!("ld.param.b64 {}, [k_{}_len];", l, n));
            params.push(format!(".param .b64 k_{}", n));
            params.push(format!(".param .b64 k_{}_len", n));
            px.arrs.insert(n.clone(), Arr { ptr: d, len: l, elem });
            arrays.push((n.clone(), elem, written.contains(n)));
        } else if scalar_ok(*ty) {
            let d = if *ty == Ty::F32 { px.freg() } else { px.rd() };
            px.i(&format!("ld.param.{} {}, [k_{}];", pty(*ty), d, n));
            params.push(format!(".param .{} k_{}", pty(*ty), n));
            px.vals.insert(n.clone(), d);
            scalars.push((n.clone(), *ty));
        } else {
            return Err(format!("uses '{}' of type {}", n, ty.name()));
        }
    }
    px.block(body)?;
    px.out += "$Lexit:\n\tret;\n";
    let entry = format!(".visible .entry {}({})\n{{\n{}{}}}\n", name, params.join(", "), px.regs(), px.out);
    // Every callee, transitively, must compile too.
    let mut callees = px.callees.clone();
    let mut work: Vec<String> = callees.iter().cloned().collect();
    while let Some(c) = work.pop() {
        let (_, more) = func(prog, funcs, funcs[c.as_str()])?;
        for m in more {
            if callees.insert(m.clone()) {
                work.push(m);
            }
        }
    }
    Ok(Kernel { name, entry, callees, scalars, arrays })
}

/// The whole PTX module for a program's kernels.
pub fn module(prog: &Program, funcs: &HashMap<&str, &Func>, kernels: &[Kernel]) -> String {
    let mut all: BTreeSet<String> = BTreeSet::new();
    kernels.iter().for_each(|k| all.extend(k.callees.iter().cloned()));
    let mut s = String::from("// Generated by keel: one kernel per par for loop.\n.version 7.0\n.target sm_70\n.address_size 64\n\n");
    for c in &all {
        s += &func_header(funcs[c.as_str()]).unwrap();
        s += ";\n";
    }
    for c in &all {
        s += "\n";
        s += &func(prog, funcs, funcs[c.as_str()]).unwrap().0;
    }
    for k in kernels {
        s += "\n";
        s += &k.entry;
    }
    s
}
