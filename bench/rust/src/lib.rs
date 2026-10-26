//! Shared helpers for the Rust twins of the Bend benchmarks. Every binary
//! takes one argument, `seq` or `par`: `seq` runs the same algorithm on
//! one thread, `par` forks with `rayon::join` at the same points where the
//! Keel program uses `par`.

pub fn parallel() -> bool {
    match std::env::args().nth(1).as_deref() {
        Some("seq") => false,
        Some("par") => true,
        _ => {
            eprintln!("usage: {} seq|par", std::env::args().next().unwrap());
            std::process::exit(2);
        }
    }
}

/// Run `a` and `b`, in parallel when `par`.
#[inline]
pub fn join<A, B, RA, RB>(par: bool, a: A, b: B) -> (RA, RB)
where
    A: FnOnce() -> RA + Send,
    B: FnOnce() -> RB + Send,
    RA: Send,
    RB: Send,
{
    if par {
        rayon::join(a, b)
    } else {
        (a(), b())
    }
}
