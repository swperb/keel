// C backend. Specs, asserts and quantifiers are erased; every safety
// property was proven, so no bounds, overflow or null checks are emitted.
// Exclusive borrows become `restrict` pointers, which C compilers exploit
// for vectorization.

use crate::ast::*;
use std::collections::HashMap;

const RUNTIME: &str = r#"#define _DEFAULT_SOURCE /* glibc: keep clock_gettime, sysconf, dlopen visible under -std=c11 */
#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <stdatomic.h>
#include <unistd.h>

/* An owned array of T and its allocator, per element type. */
#define KL_ARR(T, S) \
typedef struct { T* data; int64_t len; } klrt_arr##S; \
static T* klrt_alloc##S(int64_t n, int64_t fill) { \
    T* p = (T*)calloc(n ? (size_t)n : 1, sizeof(T)); \
    if (!p) { fputs("keel: out of memory\n", stderr); exit(70); } \
    if (fill != 0) for (int64_t i = 0; i < n; i++) p[i] = (T)fill; \
    return p; \
}
KL_ARR(int64_t, )
KL_ARR(int32_t, _i32)
KL_ARR(int16_t, _i16)
KL_ARR(int8_t, _i8)
KL_ARR(uint32_t, _u32)
KL_ARR(uint16_t, _u16)
KL_ARR(uint8_t, _u8)
KL_ARR(float, _f32)

/* f32 -> i64 toward zero, saturating, NaN -> 0: defined for every input
   (C's own conversion is undefined out of range). Same rule as PTX cvt. */
static int64_t klrt_f2i(float x) {
    if (x != x) return 0;
    if (x >= 0x1p63f) return INT64_MAX;
    if (x < -0x1p63f) return INT64_MIN;
    return (int64_t)x;
}
static int64_t klrt_fbits(float x) {
    uint32_t b;
    memcpy(&b, &x, sizeof b);
    return (int64_t)b;
}

/* par: spawn only while a core is free, otherwise run inline. */
static atomic_int klrt_live = 1;
static int klrt_max = 1;
static pthread_attr_t klrt_attr;
static void klrt_rt_init(void) {
    long n = sysconf(_SC_NPROCESSORS_ONLN);
    klrt_max = n > 0 ? (int)n : 1;
    pthread_attr_init(&klrt_attr);
    pthread_attr_setstacksize(&klrt_attr, 64u << 20);
}
static int klrt_spawn(pthread_t* t, void* (*f)(void*), void* a) {
    int c = atomic_load_explicit(&klrt_live, memory_order_relaxed);
    while (c < klrt_max) {
        if (atomic_compare_exchange_weak(&klrt_live, &c, c + 1)) {
            if (pthread_create(t, &klrt_attr, f, a) == 0) return 1;
            atomic_fetch_sub(&klrt_live, 1);
            break;
        }
    }
    f(a);
    return 0;
}
static void klrt_join(pthread_t t, int spawned) {
    if (spawned) { pthread_join(t, NULL); atomic_fetch_sub(&klrt_live, 1); }
}
"#;

/// Host side of the GPU path, included only when some `par for` became a
/// kernel. The CUDA driver is loaded at run time with dlopen, so the program
/// builds and runs anywhere; without a driver or device every loop runs on
/// the CPU. KEEL_GPU=0 forces the CPU; KEEL_GPU_TIMING=1 prints per-launch
/// copy and kernel times.
const GPU_RUNTIME: &str = r#"#include <dlfcn.h>
#include <time.h>
typedef unsigned long long klrt_dev;
#define KLRT_GPU_MAX ((uint64_t)2147483647 * 256)
static const char klrt_ptx[];
static struct {
    atomic_int state; /* 0 untried, 1 ready, -1 off */
    void* ctx; void* mod; int timing;
    int (*Init)(unsigned);
    int (*DeviceGetCount)(int*);
    int (*DeviceGet)(int*, int);
    int (*PrimaryCtxRetain)(void**, int);
    int (*CtxSetCurrent)(void*);
    int (*ModuleLoadDataEx)(void**, const void*, unsigned, int*, void**);
    int (*ModuleGetFunction)(void**, void*, const char*);
    int (*MemAlloc)(klrt_dev*, size_t);
    int (*MemFree)(klrt_dev);
    int (*HtoD)(klrt_dev, const void*, size_t);
    int (*DtoH)(void*, klrt_dev, size_t);
    int (*Launch)(void*, unsigned, unsigned, unsigned, unsigned, unsigned, unsigned, unsigned, void*, void**, void**);
    int (*Sync)(void);
} klrt_gpu;
static pthread_mutex_t klrt_gpu_mu = PTHREAD_MUTEX_INITIALIZER;
static double klrt_now(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (double)t.tv_sec + (double)t.tv_nsec * 1e-9;
}
static void klrt_gpu_setup(void) {
    const char* want = getenv("KEEL_GPU");
    if (want && strcmp(want, "0") == 0) return;
    void* h = dlopen("libcuda.so.1", RTLD_NOW | RTLD_LOCAL);
    if (!h) h = dlopen("libcuda.so", RTLD_NOW | RTLD_LOCAL);
    if (!h) {
        if (want) fputs("keel: note: KEEL_GPU is set but no CUDA driver was found; par for loops run on the CPU\n", stderr);
        return;
    }
#define KLRT_SYM(f, s) if (!(*(void**)&klrt_gpu.f = dlsym(h, s))) { fputs("keel: note: the CUDA driver is too old; par for loops run on the CPU\n", stderr); return; }
    KLRT_SYM(Init, "cuInit") KLRT_SYM(DeviceGetCount, "cuDeviceGetCount") KLRT_SYM(DeviceGet, "cuDeviceGet")
    KLRT_SYM(PrimaryCtxRetain, "cuDevicePrimaryCtxRetain") KLRT_SYM(CtxSetCurrent, "cuCtxSetCurrent")
    KLRT_SYM(ModuleLoadDataEx, "cuModuleLoadDataEx") KLRT_SYM(ModuleGetFunction, "cuModuleGetFunction")
    KLRT_SYM(MemAlloc, "cuMemAlloc_v2") KLRT_SYM(MemFree, "cuMemFree_v2") KLRT_SYM(HtoD, "cuMemcpyHtoD_v2")
    KLRT_SYM(DtoH, "cuMemcpyDtoH_v2") KLRT_SYM(Launch, "cuLaunchKernel") KLRT_SYM(Sync, "cuCtxSynchronize")
    int n = 0, dev = 0;
    if (klrt_gpu.Init(0) || klrt_gpu.DeviceGetCount(&n) || n < 1 || klrt_gpu.DeviceGet(&dev, 0)
        || klrt_gpu.PrimaryCtxRetain(&klrt_gpu.ctx, dev) || klrt_gpu.CtxSetCurrent(klrt_gpu.ctx)) {
        if (want) fputs("keel: note: no usable CUDA device; par for loops run on the CPU\n", stderr);
        return;
    }
    static char log[16384];
    int opts[2] = { 5, 6 }; /* CU_JIT_ERROR_LOG_BUFFER, CU_JIT_ERROR_LOG_BUFFER_SIZE_BYTES */
    void* vals[2] = { log, (void*)(size_t)sizeof log };
    if (klrt_gpu.ModuleLoadDataEx(&klrt_gpu.mod, klrt_ptx, 2, opts, vals)) {
        fprintf(stderr, "keel: note: the CUDA driver rejected keel's kernels (a keel bug); par for loops run on the CPU\n%s\n", log);
        return;
    }
    klrt_gpu.timing = getenv("KEEL_GPU_TIMING") != NULL;
    atomic_store(&klrt_gpu.state, 1);
}
static int klrt_gpu_init(void) {
    int s = atomic_load(&klrt_gpu.state);
    if (s == 0) {
        pthread_mutex_lock(&klrt_gpu_mu);
        if (atomic_load(&klrt_gpu.state) == 0) {
            klrt_gpu_setup();
            if (atomic_load(&klrt_gpu.state) == 0) atomic_store(&klrt_gpu.state, -1);
        }
        pthread_mutex_unlock(&klrt_gpu_mu);
        s = atomic_load(&klrt_gpu.state);
    }
    /* The context must be current on whichever thread launches. */
    return s > 0 && !klrt_gpu.CtxSetCurrent(klrt_gpu.ctx);
}
static int klrt_gpu_fn(void** fn, const char* name) {
    pthread_mutex_lock(&klrt_gpu_mu);
    if (!*fn && klrt_gpu.ModuleGetFunction(fn, klrt_gpu.mod, name)) *fn = NULL;
    pthread_mutex_unlock(&klrt_gpu_mu);
    return *fn != NULL;
}
static int klrt_gpu_put(klrt_dev* d, const void* p, size_t n) {
    if (klrt_gpu.MemAlloc(d, n ? n : 1)) { *d = 0; return 0; }
    return n == 0 || !klrt_gpu.HtoD(*d, p, n);
}
static int klrt_gpu_launch(void* fn, uint64_t n, void** args) {
    unsigned b = 256;
    if (!klrt_gpu.Launch(fn, (unsigned)((n + b - 1) / b), 1, 1, b, 1, 1, 0, NULL, args, NULL) && !klrt_gpu.Sync()) return 1;
    /* A failed launch can leave the context unusable: stop using the GPU. */
    if (atomic_exchange(&klrt_gpu.state, -1) > 0) fputs("keel: note: a GPU kernel failed (a keel bug); par for loops run on the CPU\n", stderr);
    return 0;
}
/* After a launch succeeded the host arrays may no longer be rerun on the
   CPU (an in-place update would apply twice), so a failed copy is fatal. */
static void klrt_gpu_get(void* p, klrt_dev d, size_t n) {
    if (n && klrt_gpu.DtoH(p, d, n)) { fputs("keel: copying a result back from the GPU failed\n", stderr); exit(70); }
}
static void klrt_gpu_free(klrt_dev d) {
    if (d) klrt_gpu.MemFree(d);
}
static void klrt_gpu_report(const char* k, uint64_t n, int ok, double t0, double t1, double t2, double t3) {
    if (klrt_gpu.timing)
        fprintf(stderr, "keel: gpu %s n=%llu %s: copy in %.2f ms, kernel %.2f ms, copy out %.2f ms\n", k, (unsigned long long)n,
                ok ? "ok" : "FAILED (ran on the CPU)", (t1 - t0) * 1e3, (t2 - t1) * 1e3, (t3 - t2) * 1e3);
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
    /// Element type of the array an `array(n, fill)` call is bound to.
    arr_elem: IntK,
    /// Types of the variables in scope, per lexical scope.
    tys: Vec<HashMap<String, Ty>>,
    /// GPU kernels compiled from `par for` bodies.
    kernels: Vec<crate::ptx::Kernel>,
    /// Why some `par for` loops stay on the CPU.
    notes: Vec<String>,
}

/// Suffix naming the C array struct and allocator for an element type.
fn arr_suffix(k: IntK) -> String {
    if k == IntK::I64 {
        String::new()
    } else {
        format!("_{}", k.name())
    }
}

fn cty(t: Ty) -> String {
    match t {
        Ty::Int(k) => k.cname(),
        Ty::F32 => "float".into(),
        Ty::Bool => "bool".into(),
        Ty::Unit => "void".into(),
        Ty::Named(id) => format!("kt_{}", type_name(id)),
        Ty::Payload(id, v) => format!("kt_{}_v{}", type_name(id), v),
        Ty::ArrOf(k) | Ty::RefOf(k) | Ty::RefMutOf(k) => format!("klrt_arr{}", arr_suffix(k)),
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
            Ty::RefOf(k) => v.push(format!("const {1}* restrict k_{0}, int64_t k_{0}_len", p.name, k.cname())),
            Ty::RefMutOf(k) => v.push(format!("{1}* restrict k_{0}, int64_t k_{0}_len", p.name, k.cname())),
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

    fn f32_expr(&self, e: &Expr) -> bool {
        let var = |n: &str| self.tys.iter().rev().find_map(|m| m.get(n).copied());
        is_f32(e, &var, &|n| self.funcs.get(n).map(|f| f.ret))
    }

    fn ex(&mut self, e: &Expr) -> String {
        if self.f32_expr(e) {
            // IEEE f32 arithmetic: no int64 promotion. Built with
            // -ffp-contract=off so a * b + c rounds twice, as in PTX.
            match &e.k {
                ExprK::Float(v) => return format!("({:?}f)", v),
                ExprK::Unary(UOp::Neg, a) => return format!("(-{})", self.ex(a)),
                ExprK::Binary(op, a, b) => {
                    let (a, b) = (self.ex(a), self.ex(b));
                    return format!("({} {} {})", a, op.sym(), b);
                }
                _ => {}
            }
        }
        if let ExprK::Binary(op, a, b) = &e.k {
            if self.f32_expr(a) {
                let (a, b) = (self.ex(a), self.ex(b));
                return format!("({} {} {})", a, op.sym(), b);
            }
        }
        match &e.k {
            ExprK::Float(_) => unreachable!(),
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
            ExprK::Unary(UOp::Neg, a) => format!("(-(int64_t){})", self.ex(a)),
            ExprK::Unary(UOp::Not, a) => format!("(!{})", self.ex(a)),
            ExprK::Unary(UOp::BitNot, a) => format!("(~(int64_t){})", self.ex(a)),
            ExprK::Binary(op, a, b) => {
                let (a, b) = (self.ex(a), self.ex(b));
                // Keel computes in i64. C would compute narrow operands in
                // int, or in unsigned for u32, so promote every operand.
                let (a, b) = match op {
                    BOp::And | BOp::Or | BOp::Implies => (a, b),
                    _ => (format!("(int64_t){}", a), format!("(int64_t){}", b)),
                };
                match op {
                    BOp::Implies => format!("(!{} || {})", a, b),
                    // Shifting a negative value left is undefined in C; the
                    // unsigned shift is not, and equals a * 2^b when that fits,
                    // which the verifier proved. Right shift of a negative
                    // value is arithmetic on every supported compiler.
                    BOp::Shl => format!("((int64_t)((uint64_t){} << {}))", a, b),
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
            "to_f32" => format!("((float)(int64_t){})", self.ex(&args[0])),
            "to_i64" => format!("klrt_f2i({})", self.ex(&args[0])),
            "f32_bits" => format!("klrt_fbits({})", self.ex(&args[0])),
            "array" => {
                let n = self.ex(&args[0]);
                let fill = self.ex(&args[1]);
                let s = arr_suffix(self.arr_elem);
                format!("((klrt_arr{2}){{klrt_alloc{2}({0}, {1}), {0}}})", n, fill, s)
            }
            _ if crate::check::wrap_kind(name).is_some() => {
                let k = crate::check::wrap_kind(name).unwrap();
                format!("(({})({}))", k.cname(), self.ring(&args[0]))
            }
            _ => format!("kl_{}({})", name, self.args(args).join(", ")),
        }
    }

    /// The + - * spine of a wrap_<type>(..) argument in uint64_t, which
    /// wraps modulo 2^64 and so is exact modulo any narrower 2^N.
    fn ring(&mut self, e: &Expr) -> String {
        match &e.k {
            ExprK::Binary(op @ (BOp::Add | BOp::Sub | BOp::Mul), a, b) => format!("({} {} {})", self.ring(a), op.sym(), self.ring(b)),
            ExprK::Unary(UOp::Neg, a) => format!("((uint64_t)0 - {})", self.ring(a)),
            _ => format!("((uint64_t)(int64_t){})", self.ex(e)),
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
        self.tys.push(HashMap::new());
        for s in b {
            self.stmt(s);
        }
        let ends_in_return = matches!(b.last().map(|s| &s.k), Some(StmtK::Return(_)));
        if !ends_in_return {
            let top = self.owned.len() - 1;
            self.free_scopes(top, None);
        }
        self.owned.pop();
        self.tys.pop();
    }

    fn declare(&mut self, name: &str, ty: Ty) {
        self.tys.last_mut().unwrap().insert(name.to_string(), ty);
    }

    fn stmt(&mut self, s: &Stmt) {
        match &s.k {
            StmtK::Let { name, ty, init, .. } => {
                self.declare(name, *ty);
                if let Ty::ArrOf(k) = *ty {
                    self.arr_elem = k;
                    let v = self.ex(init);
                    self.arr_elem = IntK::I64;
                    self.tmp += 1;
                    let t = self.tmp;
                    self.line(&format!("{} t{} = {};", cty(*ty), t, v));
                    self.line(&format!("{2}* restrict k_{0} = t{1}.data; const int64_t k_{0}_len = t{1}.len;", name, t, k.cname()));
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
                        self.declare(b, Ty::Payload(*enum_id, i as u32));
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
                        self.line(&format!("{} r{} = {{k_{2}, k_{2}_len}};", cty(self.cur_ret), t, n));
                        Some(n.clone())
                    }
                    _ => {
                        let ret = self.cur_ret;
                        self.arr_elem = ret.elem().unwrap_or(IntK::I64);
                        let v = self.ex(e);
                        self.arr_elem = IntK::I64;
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
            StmtK::ParFor { var, lo, hi, body, .. } => {
                // The verifier proved no iteration touches a slot another
                // writes, and the body assigns only its own locals, so every
                // outer variable is safely shared. Without OpenMP the pragma
                // is ignored and the loop runs serially, with the same result.
                let (l, h) = (self.ex(lo), self.ex(hi));
                self.tmp += 1;
                let t = self.tmp;
                self.line(&format!("const int64_t lo{0} = {1}, hi{0} = {2};", t, l, h));
                // On a GPU when one is present; the CPU loop otherwise.
                let outer: HashMap<String, Ty> = self.tys.iter().flat_map(|m| m.iter().map(|(k, v)| (k.clone(), *v))).collect();
                let gpu = match crate::ptx::kernel(self.prog, &self.funcs, t, var, body, &outer) {
                    Ok(k) => {
                        let call = self.launcher(&k, t);
                        self.kernels.push(k);
                        Some(call)
                    }
                    Err(why) => {
                        self.notes.push(format!("par for at line {}:{} runs on the CPU only: its body {}", s.span.line, s.span.col, why));
                        None
                    }
                };
                if let Some(call) = &gpu {
                    self.line(&format!("if (!{}) {{", call));
                    self.ind += 1;
                }
                self.line("#pragma omp parallel for schedule(static)");
                self.line(&format!("for (int64_t k_{1} = lo{0}; k_{1} < hi{0}; k_{1}++) {{", t, var));
                self.ind += 1;
                self.block(body);
                self.ind -= 1;
                self.line("}");
                if gpu.is_some() {
                    self.ind -= 1;
                    self.line("}");
                }
            }
        }
    }

    fn par(&mut self, branches: &[ParBranch]) {
        self.tmp += 1;
        let id = self.tmp;
        let mut structs = vec![];
        for (bi, b) in branches.iter().enumerate() {
            let ExprK::Call(fname, args) = &b.call.k else { unreachable!() };
            let g = self.funcs[fname.as_str()];
            let sname = format!("klrt_par{}_{}", id, bi);
            let mut fields = vec![];
            let mut inits = vec![];
            let mut call_args = vec![];
            for (ai, (a, p)) in args.iter().zip(&g.params).enumerate() {
                match p.ty {
                    Ty::RefOf(k) | Ty::RefMutOf(k) => {
                        let q = if matches!(p.ty, Ty::RefOf(_)) { "const " } else { "" };
                        fields.push(format!("{}{}* a{}; int64_t a{}l;", q, k.cname(), ai, ai));
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
            self.line(&format!("pthread_t th{0}_{1}; int sp{0}_{1} = klrt_spawn(&th{0}_{1}, {2}_run, &p{0}_{1});", id, bi, structs[bi]));
        }
        self.line(&format!("{}_run(&p{}_{});", structs[last], id, last));
        for bi in 0..last {
            self.line(&format!("klrt_join(th{0}_{1}, sp{0}_{1});", id, bi));
        }
        for (bi, b) in branches.iter().enumerate() {
            if let Some(n) = &b.name {
                self.line(&format!("{} k_{} = p{}_{}.r;", cty(b.ty), n, id, bi));
                self.declare(n, b.ty);
            }
        }
    }
}

impl<'a> Cg<'a> {
    /// A host function that runs kernel `k` on the GPU: copy every array it
    /// uses to the device, launch one thread per iteration, copy written
    /// arrays back. It returns 0, having changed nothing, when there is no
    /// usable GPU; the caller then runs the CPU loop. Returns the call.
    fn launcher(&mut self, k: &crate::ptx::Kernel, t: usize) -> String {
        let mut ps = vec!["int64_t lo".to_string(), "int64_t hi".to_string()];
        let mut call = vec![format!("lo{}", t), format!("hi{}", t)];
        let mut args = vec!["&lo".to_string(), "&n".to_string()];
        for (sname, ty) in &k.scalars {
            // An f32 kernel parameter is a float; every other scalar is 64 bits.
            let ct = if *ty == Ty::F32 { "float" } else { "int64_t" };
            ps.push(format!("{} s_{}", ct, sname));
            call.push(format!("({})k_{}", ct, sname));
            args.push(format!("&s_{}", sname));
        }
        let mut body = String::new();
        let (mut puts, mut gets) = (vec![], vec![]);
        for (j, (a, elem, w)) in k.arrays.iter().enumerate() {
            ps.push(format!("{}{}* a_{}, int64_t a_{}_len", if *w { "" } else { "const " }, elem.cname(), a, a));
            call.push(format!("k_{}, k_{}_len", a, a));
            args.push(format!("&d[{}]", j));
            args.push(format!("&a_{}_len", a));
            let bytes = format!("(size_t)a_{}_len * sizeof({})", a, elem.cname());
            puts.push(format!("    ok = ok && klrt_gpu_put(&d[{}], a_{}, {});\n", j, a, bytes));
            if *w {
                gets.push(format!("    if (ok) klrt_gpu_get(a_{}, d[{}], {});\n", a, j, bytes));
            }
        }
        let nd = k.arrays.len().max(1);
        body += &format!("static int klrt_{}({}) {{\n", k.name, ps.join(", "));
        body += "    if (hi <= lo || !klrt_gpu_init()) return 0;\n";
        body += "    uint64_t n = (uint64_t)hi - (uint64_t)lo;\n";
        body += &format!("    static void* fn;\n    if (n > KLRT_GPU_MAX || !klrt_gpu_fn(&fn, \"{}\")) return 0;\n", k.name);
        body += &format!("    klrt_dev d[{}] = {{0}};\n    int ok = 1;\n    double t0 = klrt_now();\n", nd);
        body += &puts.concat();
        body += &format!("    double t1 = klrt_now();\n    void* args[] = {{ {} }};\n    ok = ok && klrt_gpu_launch(fn, n, args);\n    double t2 = klrt_now();\n", args.join(", "));
        body += &gets.concat();
        body += &format!("    for (int j = 0; j < {}; j++) klrt_gpu_free(d[j]);\n", nd);
        body += &format!("    klrt_gpu_report(\"{}\", n, ok, t0, t1, t2, klrt_now());\n    return ok;\n}}\n", k.name);
        self.thunks += &body;
        format!("klrt_{}({})", k.name, call.join(", "))
    }
}

/// C string literal holding `text`, one source line per line of text.
fn c_string(text: &str) -> String {
    text.lines().map(|l| format!("\"{}\\n\"\n", l.replace('\\', "\\\\").replace('"', "\\\""))).collect()
}

pub fn emit(prog: &Program) -> (String, Vec<String>) {
    let all = &prog.funcs;
    // Spec fns and lemmas are mathematics: nothing to emit.
    let funcs: Vec<&Func> = all.iter().filter(|f| f.kind == FnKind::Code).collect();
    let mut cg = Cg { prog, funcs: all.iter().map(|f| (f.name.as_str(), f)).collect(), out: String::new(), thunks: String::new(), ind: 0, tmp: 0, owned: vec![], cur_ret: Ty::Unit, arr_elem: IntK::I64, tys: vec![], kernels: vec![], notes: vec![] };
    let mut protos = String::new();
    for f in &funcs {
        protos += &format!("static {} kl_{}({});\n", cty(f.ret), f.name, params_c(f));
    }
    for f in &funcs {
        cg.cur_ret = f.ret;
        cg.tys = vec![f.params.iter().map(|p| (p.name.clone(), p.ty)).collect()];
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
    if !cg.kernels.is_empty() {
        c += GPU_RUNTIME;
        c += "static const char klrt_ptx[] =\n";
        c += &c_string(&crate::ptx::module(prog, &cg.funcs, &cg.kernels));
        c += ";\n\n";
    }
    c += &cg.thunks;
    c += "\n";
    c += &cg.out;
    if funcs.iter().any(|f| f.name == "main") {
        c += "int main(void) {\n    klrt_rt_init();\n    kl_main();\n    return 0;\n}\n";
    }
    (c, cg.notes)
}
