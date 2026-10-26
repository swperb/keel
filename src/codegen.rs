// C backend. Specs, asserts and quantifiers are erased; every safety
// property was proven, so no bounds, overflow or null checks are emitted.
// Exclusive borrows become `restrict` pointers, which C compilers exploit
// for vectorization.

use crate::ast::*;
use std::collections::HashMap;

const RUNTIME: &str = r#"#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <stdatomic.h>
#include <unistd.h>

typedef struct { int64_t* data; int64_t len; } kl_arr;

static int64_t* kl_alloc(int64_t n, int64_t fill) {
    int64_t* p = fill == 0 ? (int64_t*)calloc(n ? (size_t)n : 1, 8) : (int64_t*)malloc((n ? (size_t)n : 1) * 8);
    if (!p) { fputs("keel: out of memory\n", stderr); exit(70); }
    if (fill != 0) for (int64_t i = 0; i < n; i++) p[i] = fill;
    return p;
}

/* par: spawn only while a core is free, otherwise run inline. */
static atomic_int kl_live = 1;
static int kl_max = 1;
static pthread_attr_t kl_attr;
static void kl_rt_init(void) {
    long n = sysconf(_SC_NPROCESSORS_ONLN);
    kl_max = n > 0 ? (int)n : 1;
    pthread_attr_init(&kl_attr);
    pthread_attr_setstacksize(&kl_attr, 64u << 20);
}
static int kl_spawn(pthread_t* t, void* (*f)(void*), void* a) {
    int c = atomic_load_explicit(&kl_live, memory_order_relaxed);
    while (c < kl_max) {
        if (atomic_compare_exchange_weak(&kl_live, &c, c + 1)) {
            if (pthread_create(t, &kl_attr, f, a) == 0) return 1;
            atomic_fetch_sub(&kl_live, 1);
            break;
        }
    }
    f(a);
    return 0;
}
static void kl_join(pthread_t t, int spawned) {
    if (spawned) { pthread_join(t, NULL); atomic_fetch_sub(&kl_live, 1); }
}
"#;

struct Cg<'a> {
    prog: &'a Program,
    funcs: HashMap<&'a str, &'a Func>,
    out: String,
    thunks: String,
    ind: usize,
    tmp: usize,
    /// Owned arrays per lexical scope, freed at scope exit.
    owned: Vec<Vec<String>>,
    /// Return type of the function being emitted.
    cur_ret: Ty,
}

fn cty(t: Ty) -> String {
    match t {
        Ty::I64 => "int64_t".into(),
        Ty::Bool => "bool".into(),
        Ty::Unit => "void".into(),
        Ty::Named(id) => format!("kt_{}", type_name(id)),
        Ty::Payload(id, v) => format!("kt_{}_v{}", type_name(id), v),
        _ => "kl_arr".into(),
    }
}

/// C typedefs for structs and enums, dependencies first.
fn typedefs(prog: &Program) -> String {
    let mut order: Vec<u32> = vec![];
    fn visit(prog: &Program, id: u32, order: &mut Vec<u32>) {
        if order.contains(&id) {
            return;
        }
        let deps: Vec<u32> = match &prog.def(id).kind {
            TypeKind::Struct(fs) => fs.iter().filter_map(|f| if let Ty::Named(i) = f.ty { Some(i) } else { None }).collect(),
            TypeKind::Enum(vs) => vs.iter().flat_map(|v| v.fields.iter()).filter_map(|f| if let Ty::Named(i) = f.ty { Some(i) } else { None }).collect(),
        };
        for d in deps {
            visit(prog, d, order);
        }
        order.push(id);
    }
    for d in &prog.types {
        visit(prog, d.id, &mut order);
    }
    let fields = |fs: &Vec<Field>| fs.iter().map(|f| format!("{} {};", cty(f.ty), f.name)).collect::<Vec<_>>().join(" ");
    let mut out = String::new();
    for id in order {
        let d = prog.def(id);
        match &d.kind {
            TypeKind::Struct(fs) => out += &format!("typedef struct {{ {} }} kt_{};\n", fields(fs), d.name),
            TypeKind::Enum(vs) => {
                let mut members = vec![];
                for (i, v) in vs.iter().enumerate() {
                    if !v.fields.is_empty() {
                        out += &format!("typedef struct {{ {} }} kt_{}_v{};\n", fields(&v.fields), d.name, i);
                        members.push(format!("kt_{}_v{} {};", d.name, i, v.name));
                    }
                }
                let u = if members.is_empty() { String::new() } else { format!(" union {{ {} }} u;", members.join(" ")) };
                out += &format!("typedef struct {{ int32_t tag;{} }} kt_{};\n", u, d.name);
            }
        }
    }
    out
}

fn params_c(f: &Func) -> String {
    let mut v = vec![];
    for p in &f.params {
        match p.ty {
            Ty::Ref => v.push(format!("const int64_t* restrict k_{0}, int64_t k_{0}_len", p.name)),
            Ty::RefMut => v.push(format!("int64_t* restrict k_{0}, int64_t k_{0}_len", p.name)),
            t => v.push(format!("{} k_{}", cty(t), p.name)),
        }
    }
    if v.is_empty() {
        "void".into()
    } else {
        v.join(", ")
    }
}

impl<'a> Cg<'a> {
    fn line(&mut self, s: &str) {
        for _ in 0..self.ind {
            self.out += "    ";
        }
        self.out += s;
        self.out.push('\n');
    }

    fn ex(&mut self, e: &Expr) -> String {
        match &e.k {
            ExprK::Int(v) => {
                if *v == i64::MIN as i128 {
                    "INT64_MIN".into()
                } else {
                    format!("INT64_C({})", v)
                }
            }
            ExprK::Bool(b) => b.to_string(),
            ExprK::Var(n) => format!("k_{}", n),
            ExprK::Index(n, i) => format!("k_{}[{}]", n, self.ex(i)),
            ExprK::Unary(UOp::Neg, a) => format!("(-{})", self.ex(a)),
            ExprK::Unary(UOp::Not, a) => format!("(!{})", self.ex(a)),
            ExprK::Binary(op, a, b) => {
                let (a, b) = (self.ex(a), self.ex(b));
                match op {
                    BOp::Implies => format!("(!{} || {})", a, b),
                    _ => format!("({} {} {})", a, op.sym(), b),
                }
            }
            ExprK::Call(name, args) => self.call(name, args),
            ExprK::Lit { ty, variant, fields } => {
                let inits: Vec<String> = fields.iter().map(|(n, fe)| format!(".{} = {}", n, self.ex(fe))).collect();
                match variant {
                    None => format!("((kt_{}){{ {} }})", type_name(*ty), inits.join(", ")),
                    Some(v) => {
                        let vi = self.prog.variants(*ty).unwrap().iter().position(|x| x.name == *v).unwrap();
                        if inits.is_empty() {
                            format!("((kt_{}){{ .tag = {} }})", type_name(*ty), vi)
                        } else {
                            format!("((kt_{}){{ .tag = {}, .u.{} = {{ {} }} }})", type_name(*ty), vi, v, inits.join(", "))
                        }
                    }
                }
            }
            ExprK::Field(b, f) => format!("({}).{}", self.ex(b), f),
            ExprK::Is(b, id, v) => {
                let vi = self.prog.variants(*id).unwrap().iter().position(|x| x.name == *v).unwrap();
                format!("(({}).tag == {})", self.ex(b), vi)
            }
            ExprK::Result | ExprK::Quant { .. } | ExprK::Borrow { .. } | ExprK::IfE(..) | ExprK::As(..) | ExprK::Old(..) => unreachable!("specs are erased"),
        }
    }

    fn args(&mut self, args: &[Expr]) -> Vec<String> {
        let mut v = vec![];
        for a in args {
            match &a.k {
                ExprK::Borrow { .. } => {
                    let (p, l) = self.borrow(a);
                    v.push(p);
                    v.push(l);
                }
                _ => v.push(self.ex(a)),
            }
        }
        v
    }

    /// C pointer and length for a borrow; a slice is pointer arithmetic.
    fn borrow(&mut self, a: &Expr) -> (String, String) {
        let ExprK::Borrow { name, range, .. } = &a.k else { unreachable!() };
        match range {
            None => (format!("k_{}", name), format!("k_{}_len", name)),
            Some((lo, hi)) => {
                let (l, h) = (self.ex(lo), self.ex(hi));
                (format!("(k_{} + {})", name, l), format!("({} - {})", h, l))
            }
        }
    }

    fn call(&mut self, name: &str, args: &[Expr]) -> String {
        match name {
            "len" => match &args[0].k {
                ExprK::Var(n) => format!("k_{}_len", n),
                _ => unreachable!(),
            },
            "print" => format!("printf(\"%lld\\n\", (long long){})", self.ex(&args[0])),
            "array" => {
                let n = self.ex(&args[0]);
                let fill = self.ex(&args[1]);
                format!("((kl_arr){{kl_alloc({0}, {1}), {0}}})", n, fill)
            }
            _ => format!("kl_{}({})", name, self.args(args).join(", ")),
        }
    }

    fn free_scopes(&mut self, from: usize, keep: Option<&str>) {
        let names: Vec<String> = self.owned[from..].iter().flatten().cloned().collect();
        for n in names {
            if Some(n.as_str()) != keep {
                self.line(&format!("free(k_{});", n));
            }
        }
    }

    fn block(&mut self, b: &Block) {
        self.owned.push(vec![]);
        for s in b {
            self.stmt(s);
        }
        let ends_in_return = matches!(b.last().map(|s| &s.k), Some(StmtK::Return(_)));
        if !ends_in_return {
            let top = self.owned.len() - 1;
            self.free_scopes(top, None);
        }
        self.owned.pop();
    }

    fn stmt(&mut self, s: &Stmt) {
        match &s.k {
            StmtK::Let { name, ty, init, .. } => {
                if *ty == Ty::Arr {
                    let v = self.ex(init);
                    self.tmp += 1;
                    let t = self.tmp;
                    self.line(&format!("kl_arr t{} = {};", t, v));
                    self.line(&format!("int64_t* restrict k_{0} = t{1}.data; const int64_t k_{0}_len = t{1}.len;", name, t));
                    self.owned.last_mut().unwrap().push(name.clone());
                } else {
                    let v = self.ex(init);
                    self.line(&format!("{} k_{} = {};", cty(*ty), name, v));
                }
            }
            StmtK::Assign { name, path, val } => {
                let v = self.ex(val);
                let p: String = path.iter().map(|f| format!(".{}", f)).collect();
                self.line(&format!("k_{}{} = {};", name, p, v));
            }
            StmtK::Match { scrut, enum_id, arms } => {
                let v = self.ex(scrut);
                self.tmp += 1;
                let t = self.tmp;
                self.line(&format!("{} m{} = {};", cty(Ty::Named(*enum_id)), t, v));
                self.line(&format!("switch (m{}.tag) {{", t));
                for (i, a) in arms.iter().enumerate() {
                    self.line(&format!("case {}: {{", i));
                    self.ind += 1;
                    if let Some(b) = &a.binder {
                        self.line(&format!("{} k_{} = m{}.u.{};", cty(Ty::Payload(*enum_id, i as u32)), b, t, a.variant));
                    }
                    self.block(&a.body);
                    self.line("break;");
                    self.ind -= 1;
                    self.line("}");
                }
                self.line("}");
            }
            StmtK::Store { name, idx, val } => {
                let (i, v) = (self.ex(idx), self.ex(val));
                self.line(&format!("k_{}[{}] = {};", name, i, v));
            }
            StmtK::If { cond, then, els } => {
                let c = self.ex(cond);
                self.line(&format!("if ({}) {{", c));
                self.ind += 1;
                self.block(then);
                self.ind -= 1;
                if let Some(e) = els {
                    self.line("} else {");
                    self.ind += 1;
                    self.block(e);
                    self.ind -= 1;
                }
                self.line("}");
            }
            StmtK::While { cond, body, .. } => {
                let c = self.ex(cond);
                self.line(&format!("while ({}) {{", c));
                self.ind += 1;
                self.block(body);
                self.ind -= 1;
                self.line("}");
            }
            StmtK::Return(None) => {
                self.free_scopes(0, None);
                self.line("return;");
            }
            StmtK::Return(Some(e)) => {
                self.tmp += 1;
                let t = self.tmp;
                let keep = match &e.k {
                    ExprK::Var(n) if self.owned.iter().flatten().any(|x| x == n) => {
                        self.line(&format!("kl_arr r{} = {{k_{1}, k_{1}_len}};", t, n));
                        Some(n.clone())
                    }
                    _ => {
                        let ret = self.cur_ret;
                        let v = self.ex(e);
                        self.line(&format!("{} r{} = {};", cty(ret), t, v));
                        None
                    }
                };
                self.free_scopes(0, keep.as_deref());
                self.line(&format!("return r{};", t));
            }
            StmtK::Assert(_) => {}
            StmtK::Expr(e) => {
                // Lemma invocations are ghost code: erased.
                if let ExprK::Call(n, _) = &e.k {
                    if self.funcs.get(n.as_str()).map(|f| f.kind) == Some(FnKind::Lemma) {
                        return;
                    }
                }
                let v = self.ex(e);
                self.line(&format!("{};", v));
            }
            StmtK::Par(branches) => self.par(branches),
        }
    }

    fn par(&mut self, branches: &[ParBranch]) {
        self.tmp += 1;
        let id = self.tmp;
        let mut structs = vec![];
        for (bi, b) in branches.iter().enumerate() {
            let ExprK::Call(fname, args) = &b.call.k else { unreachable!() };
            let g = self.funcs[fname.as_str()];
            let sname = format!("kl_par{}_{}", id, bi);
            let mut fields = vec![];
            let mut inits = vec![];
            let mut call_args = vec![];
            for (ai, (a, p)) in args.iter().zip(&g.params).enumerate() {
                match p.ty {
                    Ty::Ref | Ty::RefMut => {
                        let q = if p.ty == Ty::Ref { "const " } else { "" };
                        fields.push(format!("{}int64_t* a{}; int64_t a{}l;", q, ai, ai));
                        let (ptr, len) = self.borrow(a);
                        inits.push(ptr);
                        inits.push(len);
                        call_args.push(format!("s->a{0}, s->a{0}l", ai));
                    }
                    t => {
                        fields.push(format!("{} a{};", cty(t), ai));
                        inits.push(self.ex(a));
                        call_args.push(format!("s->a{}", ai));
                    }
                }
            }
            let (rfield, assign) = if b.ty == Ty::Unit { (String::new(), "") } else { (format!("{} r;", cty(b.ty)), "s->r = ") };
            if fields.is_empty() && rfield.is_empty() {
                fields.push("char unused;".into());
                inits.push("0".into());
            }
            self.thunks += &format!(
                "typedef struct {{ {} {} }} {};\nstatic void* {}_run(void* p) {{ {}* s = ({}*)p; (void)s; {}kl_{}({}); return NULL; }}\n",
                fields.join(" "),
                rfield,
                sname,
                sname,
                sname,
                sname,
                assign,
                fname,
                call_args.join(", ")
            );
            self.line(&format!("{} p{}_{} = {{ {} }};", sname, id, bi, inits.join(", ")));
            structs.push(sname);
        }
        let last = branches.len() - 1;
        for bi in 0..last {
            self.line(&format!("pthread_t th{0}_{1}; int sp{0}_{1} = kl_spawn(&th{0}_{1}, {2}_run, &p{0}_{1});", id, bi, structs[bi]));
        }
        self.line(&format!("{}_run(&p{}_{});", structs[last], id, last));
        for bi in 0..last {
            self.line(&format!("kl_join(th{0}_{1}, sp{0}_{1});", id, bi));
        }
        for (bi, b) in branches.iter().enumerate() {
            if let Some(n) = &b.name {
                self.line(&format!("{} k_{} = p{}_{}.r;", cty(b.ty), n, id, bi));
            }
        }
    }
}

pub fn emit(prog: &Program) -> String {
    let all = &prog.funcs;
    // Spec fns and lemmas are mathematics: nothing to emit.
    let funcs: Vec<&Func> = all.iter().filter(|f| f.kind == FnKind::Code).collect();
    let mut cg = Cg { prog, funcs: all.iter().map(|f| (f.name.as_str(), f)).collect(), out: String::new(), thunks: String::new(), ind: 0, tmp: 0, owned: vec![], cur_ret: Ty::Unit };
    let mut protos = String::new();
    for f in &funcs {
        protos += &format!("static {} kl_{}({});\n", cty(f.ret), f.name, params_c(f));
    }
    for f in &funcs {
        cg.cur_ret = f.ret;
        cg.out += &format!("static {} kl_{}({}) {{\n", cty(f.ret), f.name, params_c(f));
        cg.ind = 1;
        cg.block(&f.body);
        cg.out += "}\n\n";
    }
    let mut c = String::from(RUNTIME);
    c += "\n";
    c += &typedefs(prog);
    c += "\n";
    c += &protos;
    c += "\n";
    c += &cg.thunks;
    c += "\n";
    c += &cg.out;
    if funcs.iter().any(|f| f.name == "main") {
        c += "int main(void) {\n    kl_rt_init();\n    kl_main();\n    return 0;\n}\n";
    }
    c
}
