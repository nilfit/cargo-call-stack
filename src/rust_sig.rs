use pest::Parser;
use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "rust_sig.pest"]
struct Sig;

// discard the uninteresting things from a sig string for a Fn, FnOnce or FnMut
// so that callsite signatures match definition signatures
pub fn clean(ll: &str) -> Result<String, failure::Error> {
    let pair = Sig::parse(Rule::rust_sig, ll)?.next().expect("unreachable");
    let mut arg_tuple = None;
    let mut res = None;
    for pair in pair.into_inner() {
        match pair.as_rule() {
            Rule::fn_args => {
                debug_assert!(arg_tuple.is_none());
                arg_tuple = pair.into_inner().last().map(|p| p.as_str());
            }
            Rule::fn_res => {
                debug_assert!(res.is_none());
                res = Some(pair.as_str());
            }
            _ => {}
        }
    }
    Ok(format!(
        "{} -> {}",
        arg_tuple.expect("missing arg"),
        res.expect("missing res")
    ))
}

#[cfg(test)]
mod tests {
    use super::{Rule, Sig};
    use pest::Parser;

    #[test]
    fn caller() {
        Sig::parse(
            Rule::rust_sig,
            r#"extern \\22rust-call\\22 fn(&dyn for<\'r> core::ops::Fn(&\'r mut u32) -> i16, (&mut u32,)) -> i16"#,
        )
        .unwrap();
    }

    #[test]
    fn callee_simple() {
        Sig::parse(
            Rule::rust_sig,
            r#"extern \\22rust-call\\22 fn(&fn(i16) -> u32 {f_i16_u32}, (i16,)) -> u32"#,
        )
        .unwrap();
    }

    #[test]
    fn callee_fnmut() {
        Sig::parse(
            Rule::rust_sig,
            r#"extern \\22rust-call\\22 fn(*mut for<\'r> fn(&\'r mut u32) -> i16 {g_u32_i16}, (&mut u32,)) -> i16"#,
        )
        .unwrap();
    }
}
