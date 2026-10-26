mod ast;
mod check;
mod codegen;
mod diag;
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

fn front(file: &str, opts: &Opts, need_main: bool) -> Vec<ast::Func> {
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
    let funcs = match parse::parse(&src) {
        Ok(f) => f,
        Err(d) => {
            report(&[d], 0);
            exit(1)
        }
    };
    let diags = check::check(&funcs, need_main);
    if !diags.is_empty() {
        report(&diags, 0);
        exit(1);
    }
    let vr = verify::verify(&funcs, opts.dump_smt.as_deref()).unwrap_or_else(|e| {
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
        eprintln!("keel: {} obligations proved in {} functions", vr.proved, funcs.len());
    }
    funcs
}

fn build(file: &str, opts: &Opts, out: &str) {
    let funcs = front(file, opts, true);
    let c = codegen::emit(&funcs);
    let cpath = format!("{}.c", out);
    std::fs::write(&cpath, &c).unwrap_or_else(|e| {
        eprintln!("keel: cannot write {}: {}", cpath, e);
        exit(2)
    });
    let cc = std::env::var("CC").unwrap_or_else(|_| "cc".into());
    let st = Command::new(&cc)
        .args(["-O3", "-std=c11", "-w", "-o", out, &cpath, "-lpthread"])
        .status()
        .unwrap_or_else(|e| {
            eprintln!("keel: cannot run {}: {}", cc, e);
            exit(2)
        });
    if !opts.emit_c {
        let _ = std::fs::remove_file(&cpath);
    }
    if !st.success() {
        eprintln!("keel: C compiler failed (this is a keel bug)");
        exit(2);
    }
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
