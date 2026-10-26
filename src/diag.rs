// Diagnostics. Every error has a stable code, a location, and (for proof
// failures) a concrete counterexample, so an agent can act on it without
// guessing.

use crate::ast::Span;

#[derive(Clone, Debug)]
pub struct Diag {
    pub code: &'static str,
    pub msg: String,
    pub span: Span,
    pub hint: Option<String>,
    pub cex: Vec<(String, String)>,
}

impl Diag {
    pub fn new(code: &'static str, span: Span, msg: impl Into<String>) -> Diag {
        Diag { code, msg: msg.into(), span, hint: None, cex: vec![] }
    }
    pub fn hint(mut self, h: impl Into<String>) -> Diag {
        self.hint = Some(h.into());
        self
    }
}

pub fn render_human(file: &str, diags: &[Diag]) -> String {
    let mut out = String::new();
    for d in diags {
        out += &format!("{}:{}:{}: error[{}]: {}\n", file, d.span.line, d.span.col, d.code, d.msg);
        if !d.cex.is_empty() {
            let parts: Vec<String> = d.cex.iter().map(|(k, v)| format!("{} = {}", k, v)).collect();
            out += &format!("  counterexample: {}\n", parts.join(", "));
        }
        if let Some(h) = &d.hint {
            out += &format!("  hint: {}\n", h);
        }
    }
    out
}

fn esc(s: &str) -> String {
    let mut o = String::with_capacity(s.len() + 2);
    o.push('"');
    for c in s.chars() {
        match c {
            '"' => o += "\\\"",
            '\\' => o += "\\\\",
            '\n' => o += "\\n",
            '\t' => o += "\\t",
            c if (c as u32) < 0x20 => o += &format!("\\u{:04x}", c as u32),
            c => o.push(c),
        }
    }
    o.push('"');
    o
}

pub fn render_json(file: &str, diags: &[Diag], proved: usize) -> String {
    let mut items = vec![];
    for d in diags {
        let mut s = format!(
            "{{\"code\":{},\"file\":{},\"line\":{},\"col\":{},\"message\":{}",
            esc(d.code),
            esc(file),
            d.span.line,
            d.span.col,
            esc(&d.msg)
        );
        if !d.cex.is_empty() {
            let kv: Vec<String> = d.cex.iter().map(|(k, v)| format!("{}:{}", esc(k), esc(v))).collect();
            s += &format!(",\"counterexample\":{{{}}}", kv.join(","));
        }
        if let Some(h) = &d.hint {
            s += &format!(",\"hint\":{}", esc(h));
        }
        s.push('}');
        items.push(s);
    }
    format!(
        "{{\"ok\":{},\"proved\":{},\"diagnostics\":[{}]}}\n",
        diags.is_empty(),
        proved,
        items.join(",")
    )
}

/// `keel explain CODE`: long-form explanation for each stable error code.
pub fn explain(code: &str) -> Option<&'static str> {
    Some(match code {
        "E-LEX" => "Unrecognized character or malformed literal.",
        "E-PARSE" => "The program does not match Keel's grammar. Keel has exactly one syntax for each construct.",
        "E-PAREN" => "Keel has no operator precedence between different arithmetic, bitwise or logical operators. \
                      `a + b * c` and `a && b || c` are rejected; write `a + (b * c)` or `(a && b) || c`. \
                      Chains of one associative operator (`a + b - c`, `a * b * c`, `a && b && c`) are fine.",
        "E-NAME" => "Unknown or duplicate name. Keel forbids shadowing: a new local, parameter or bound variable may not reuse a name that is still in scope.",
        "E-TYPE" => "Type mismatch. Keel has no implicit conversions and no overloading.",
        "E-BORROW" => "Arrays are passed to functions only as `&xs` / `&mut xs` or slices `&xs[lo..hi]` / `&mut xs[lo..hi]`. \
                       An exclusive borrow may not coexist with any other use of the same array in the same call or `par` block, \
                       unless both are slices, in which case the verifier must prove them disjoint (V-DISJOINT). \
                       A call that takes `&mut` must be a whole statement, initializer, assigned value, return value or condition, \
                       never part of a larger expression, because C does not fix the order operands and arguments are evaluated in.",
        "E-ARRAY" => "Array values (from `array(..)` or a call returning `[i64]`) may only appear as a `let` initializer or a `return` value.",
        "E-EFFECT" => "Only `io fn` functions may call `print` or other `io fn` functions. `par` branches must be pure.",
        "E-SPEC" => "Specifications (requires/ensures/invariant/decreases/assert) are pure logic: they may call `len`, `count`, `spec fn`s, and any `fn` that is pure, loop-free, non-recursive and takes no `&mut` (its body is lifted to a definition). `old(e)` is allowed in ensures, invariants and asserts. \
                     `result` is only valid in `ensures`; `forall`/`exists` only in specifications.",
        "E-MUT" => "Only `var` locals can be reassigned; only owned arrays or `&mut` parameters can be written.",
        "E-RETURN" => "A function with a return type must end in `return` on every path.",
        "E-UNREACHABLE" => "Statements after `return` are rejected.",
        "E-DISCARD" => "Expression statements must be calls returning unit. Results may not be silently discarded.",
        "E-RECURSION" => "Recursive functions need a `decreases` clause. Mutual recursion is not supported in v0.",
        "E-MAIN" => "Programs that are built must define `io fn main()`.",
        "V-OVERFLOW" => "The verifier could not prove this i64 arithmetic stays within [-2^63, 2^63-1]. \
                         Bound the operands with `requires` or a loop `invariant`. \
                         The same code covers a value stored into a narrower integer type (u8, i32, ...) that may not fit it; \
                         bound it, or wrap explicitly with wrap_<type>(..).",
        "V-DIVZERO" => "The verifier could not prove the divisor is nonzero.",
        "V-BOUNDS" => "The verifier could not prove the index is within 0 <= i < len(xs).",
        "V-REQUIRES" => "The verifier could not prove the callee's `requires` clause at this call site.",
        "V-ENSURES" => "The verifier could not prove this function's `ensures` clause on this return path, or a `par for` ensures after one iteration.",
        "V-INVARIANT-ENTRY" => "The loop invariant does not hold before the first iteration.",
        "V-INVARIANT-KEPT" => "The loop invariant is not preserved by the loop body.",
        "V-TERMINATION" => "The `decreases` measure is not proven to be non-negative and strictly decreasing.",
        "V-ASSERT" => "The verifier could not prove this `assert`.",
        "V-ALLOC" => "The verifier could not prove the array length is in 0..=2^40.",
        "E-MATCH" => "A match must list every variant of the enum exactly once, in declaration order, with a binder exactly when the variant has a payload. There is no wildcard arm.",
        "V-VACUOUS" => "The function's requires clauses can never all be true. Any ensures would then be provable from a contradiction, so this is rejected.",
        "V-DEAD" => "This branch, match arm or loop body can never execute given the conditions and invariants that guard it. Dead code hides untested logic; delete it or fix the guard.",
        "V-SHIFT" => "A shift amount may be negative or at least 64. In C such a shift is undefined; prove 0 <= amount < 64 with a requires clause or a test.",
        "V-SLICE" => "The verifier could not prove a slice's bounds satisfy 0 <= lo <= hi <= len(array).",
        "V-DISJOINT" => "Two borrows of one array, at least one exclusive, may touch overlapping indices: in one call, or across par branches (a data race). Prove the slice ranges disjoint, e.g. [lo..mid] and [mid..hi].",
        "E-PARFOR" => "A `par for` body runs once per index, in parallel. It may compute with locals declared inside it, read any array, \
                       write `&mut` (or owned) arrays, and call non-io, non-recursive fns that do not return arrays. It may not assign a variable \
                       declared outside it (loop-carried state), print or call io fns, allocate, `return`, or contain `par` or another `par for`.",
        "V-RACE" => "Two iterations of a `par for` may touch the same array slot and at least one writes it, or the loop's `ensures` reads a slot \
                     another iteration writes. Index writes by the loop variable injectively (xs[i], xs[2 * i + 1], out[r * w + c] with 0 <= c < w), \
                     and read other slots only of arrays the loop does not write. The counterexample names two iterations i and i'.",
        "V-UNKNOWN" => "The solver used up its fixed work budget, or rejected the proof script. Budgets count solver steps, not seconds, so the verdict is the same on every run. A quantifier that reads xs[t] and xs[t + 1] can make the solver instantiate it forever; state such facts pairwise (forall a in lo..hi { forall b in a..hi { .. } }). Otherwise strengthen invariants or split the function. A rejected script is a keel bug.",
        _ => return None,
    })
}
