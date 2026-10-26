mod ast;
mod check;
mod codegen;
mod diag;
mod lift;
mod parse;
mod verify;

use std::process::{exit, Command};

const USAGE: &str = "keel: a verified systems language for agents

usage:
  keel check <file.kl> [--json]          type-check and prove the program
  keel build <file.kl> [-o out] [--emit-c] [--json]
  keel run   <file.kl> [--json]          build to a temp dir and run
  keel explain <CODE>                    explain an error code (e.g. V-OVERFLOW)

Every program that compiles is proven free of overflow, out-of-bounds access,
division by zero, contract violations, data races and non-termination.
";

struct Opts {
    json: bool,
    emit_c: bool,
    out: Option<String>,
    dump_smt: Option<String>,
}

fn front(file: &str, opts: &Opts, need_main: bool) -> ast::Program {
    let src = std::fs::read_to_string(file).unwrap_or_else(|e| {
        eprintln!("keel: cannot read {}: {}", file, e);
        exit(2)
    });
    let report = |diags: &[diag::Diag], proved: usize| {
        if opts.json {
            print!("{}", diag::render_json(file, diags, proved));
        } else {
            eprint!("{}", diag::render_human(file, diags));
        }
    };
    let prog = match parse::parse(&src) {
        Ok(f) => f,
        Err(d) => {
            report(&[d], 0);
            exit(1)
        }
    };
    let diags = check::check(&prog, need_main);
    if !diags.is_empty() {
        report(&diags, 0);
        exit(1);
    }
    let vr = verify::verify(&prog, opts.dump_smt.as_deref()).unwrap_or_else(|e| {
        eprintln!("keel: {}", e);
        exit(2)
    });
    if !vr.diags.is_empty() {
        report(&vr.diags, vr.proved);
        exit(1);
    }
    if opts.json {
        print!("{}", diag::render_json(file, &[], vr.proved));
    } else {
        eprintln!("keel: {} obligations proved in {} functions", vr.proved, prog.funcs.len());
        if vr.inconclusive > 0 {
            eprintln!("keel: note: {} reachability check(s) inconclusive (could not confirm the path is possible)", vr.inconclusive);
        }
    }
    prog
}

fn build(file: &str, opts: &Opts, out: &str) {
    let prog = front(file, opts, true);
    let c = codegen::emit(&prog);
    let cpath = format!("{}.c", out);
    std::fs::write(&cpath, &c).unwrap_or_else(|e| {
        eprintln!("keel: cannot write {}: {}", cpath, e);
        exit(2)
    });
    let cc = std::env::var("CC").unwrap_or_else(|_| "cc".into());
    let compile = |extra: &[String]| {
        Command::new(&cc)
            .args(["-O3", "-std=c11", "-w", "-o", out, &cpath, "-lpthread"])
            .args(extra)
            .stderr(if extra.is_empty() { std::process::Stdio::inherit() } else { std::process::Stdio::null() })
            .status()
            .unwrap_or_else(|e| {
                eprintln!("keel: cannot run {}: {}", cc, e);
                exit(2)
            })
    };
    // `par for` loops run on OpenMP when the C compiler has it; otherwise
    // the pragma is ignored and they run serially (same results).
    let mut st = None;
    if c.contains("#pragma omp") && std::env::var("KEEL_NO_OPENMP").is_err() {
        st = openmp_flags().iter().map(|f| compile(f)).find(|s| s.success());
        if st.is_none() {
            eprintln!("keel: note: no OpenMP found for {}; par for loops will run serially (on macOS: brew install libomp)", cc);
        }
    }
    let st = st.unwrap_or_else(|| compile(&[]));
    if !opts.emit_c {
        let _ = std::fs::remove_file(&cpath);
    }
    if !st.success() {
        eprintln!("keel: C compiler failed (this is a keel bug)");
        exit(2);
    }
}

/// Compiler flags to try for OpenMP: GCC and LLVM clang take -fopenmp;
/// Apple clang needs the preprocessor flag and a separate libomp.
fn openmp_flags() -> Vec<Vec<String>> {
    let mut v = vec![vec!["-fopenmp".to_string()]];
    let mut prefixes: Vec<String> = std::env::var("KEEL_LIBOMP").into_iter().collect();
    prefixes.extend(["/opt/homebrew/opt/libomp", "/usr/local/opt/libomp"].map(String::from));
    for p in prefixes {
        if std::path::Path::new(&format!("{}/include/omp.h", p)).exists() {
            v.push(["-Xpreprocessor", "-fopenmp", &format!("-I{}/include", p), &format!("-L{}/lib", p), &format!("-Wl,-rpath,{}/lib", p), "-lomp"].map(String::from).to_vec());
        }
    }
    v
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut opts = Opts { json: false, emit_c: false, out: None, dump_smt: None };
    let mut pos = vec![];
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--json" => opts.json = true,
            "--emit-c" => opts.emit_c = true,
            "-o" => {
                i += 1;
                opts.out = args.get(i).cloned();
            }
            "--dump-smt" => {
                i += 1;
                opts.dump_smt = args.get(i).cloned();
            }
            a => pos.push(a.to_string()),
        }
        i += 1;
    }
    match (pos.first().map(|s| s.as_str()), pos.get(1)) {
        (Some("check"), Some(f)) => {
            front(f, &opts, false);
        }
        (Some("build"), Some(f)) => {
            let out = opts.out.clone().unwrap_or_else(|| f.trim_end_matches(".kl").to_string());
            build(f, &opts, &out);
        }
        (Some("run"), Some(f)) => {
            let dir = std::env::temp_dir().join(format!("keel-{}", std::process::id()));
            std::fs::create_dir_all(&dir).unwrap();
            let out = dir.join("prog").to_string_lossy().into_owned();
            build(f, &opts, &out);
            let st = Command::new(&out).status().expect("run");
            let _ = std::fs::remove_dir_all(&dir);
            exit(st.code().unwrap_or(1));
        }
        (Some("explain"), Some(code)) => match diag::explain(code) {
            Some(t) => println!("{}: {}", code, t),
            None => {
                eprintln!("keel: unknown code {}", code);
                exit(2)
            }
        },
        _ => {
            eprint!("{}", USAGE);
            exit(2)
        }
    }
}
