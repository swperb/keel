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
        "E-PAREN" => "Keel has no operator precedence between different arithmetic or logical operators. \
                      `a + b * c` and `a && b || c` are rejected; write `a + (b * c)` or `(a && b) || c`. \
                      Chains of one associative operator (`a + b - c`, `a * b * c`, `a && b && c`) are fine.",
        "E-NAME" => "Unknown or duplicate name. Keel forbids shadowing: a new local, parameter or bound variable may not reuse a name that is still in scope.",
        "E-TYPE" => "Type mismatch. Keel has no implicit conversions and no overloading.",
        "E-BORROW" => "Arrays are passed to functions only as `&xs` (shared) or `&mut xs` (exclusive). \
                       An exclusive borrow may not coexist with any other use of the same array in the same call or `par` block.",
        "E-ARRAY" => "Array values (from `array(..)` or a call returning `[i64]`) may only appear as a `let` initializer or a `return` value.",
        "E-EFFECT" => "Only `io fn` functions may call `print` or other `io fn` functions. `par` branches must be pure.",
        "E-SPEC" => "Specifications (requires/ensures/invariant/decreases/assert) are pure logic: no calls except `len`. \
                     `result` is only valid in `ensures`; `forall`/`exists` only in specifications.",
        "E-MUT" => "Only `var` locals can be reassigned; only owned arrays or `&mut` parameters can be written.",
        "E-RETURN" => "A function with a return type must end in `return` on every path.",
        "E-UNREACHABLE" => "Statements after `return` are rejected.",
        "E-DISCARD" => "Expression statements must be calls returning unit. Results may not be silently discarded.",
        "E-RECURSION" => "Recursive functions need a `decreases` clause. Mutual recursion is not supported in v0.",
        "E-MAIN" => "Programs that are built must define `io fn main()`.",
        "V-OVERFLOW" => "The verifier could not prove this i64 arithmetic stays within [-2^63, 2^63-1]. \
                         Bound the operands with `requires` or a loop `invariant`.",
        "V-DIVZERO" => "The verifier could not prove the divisor is nonzero.",
        "V-BOUNDS" => "The verifier could not prove the index is within 0 <= i < len(xs).",
        "V-REQUIRES" => "The verifier could not prove the callee's `requires` clause at this call site.",
        "V-ENSURES" => "The verifier could not prove this function's `ensures` clause on this return path.",
        "V-INVARIANT-ENTRY" => "The loop invariant does not hold before the first iteration.",
        "V-INVARIANT-KEPT" => "The loop invariant is not preserved by the loop body.",
        "V-TERMINATION" => "The `decreases` measure is not proven to be non-negative and strictly decreasing.",
        "V-ASSERT" => "The verifier could not prove this `assert`.",
        "V-ALLOC" => "The verifier could not prove the array length is in 0..=2^40.",
        "V-UNKNOWN" => "The solver timed out. Strengthen invariants or split the function.",
        _ => return None,
    })
}
