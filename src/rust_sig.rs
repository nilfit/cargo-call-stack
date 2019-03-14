use pest::Parser;
use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "rust_sig.pest"]
struct Sig;

// discard the uninteresting things from a sig string for a Fn, FnOnce or FnMut
// so that callsite signatures match definition signatures
pub fn clean(ll: &str) -> Result<String, failure::Error> {
    Ok(_clean(ll)?.sig)
}

pub fn clean_callsite(ll: &str) -> Result<ClosureSig, failure::Error> {
    _clean(ll)
}

fn _clean(ll: &str) -> Result<ClosureSig, failure::Error> {
    eprintln!("trying to clean\n{:?}", ll);
    let pair = Sig::parse(Rule::rust_sig, ll)?.next().expect("unreachable");
    let mut arg_tuple = None;
    let mut closure_trait = None;
    let mut res = None;
    for pair in pair.into_inner() {
        match pair.as_rule() {
            Rule::fn_args => {
                debug_assert!(arg_tuple.is_none());
                let mut args = pair.into_inner();
                debug_assert_eq!(args.clone().count(), 2);

                let arg1 = args.next().unwrap().into_inner().next().unwrap();
                if arg1.as_rule() == Rule::closure_trait_arg1 {
                    //debug_assert_eq!(arg1.as_rule(), Rule::closure_trait_arg1);
                    // the part that matched Fn, FnMut or FnOnce
                    let used_trait = arg1
                        .into_inner()
                        .filter(|p| p.as_rule() == Rule::closure_trait)
                        .next()
                        .unwrap()
                        .into_inner()
                        .next()
                        .unwrap()
                        .as_rule();
                    eprintln!("++ used_trait {:?}", used_trait);
                    closure_trait = Some(ClosureTrait::from_rule(used_trait));
                }

                //arg_tuple = pair.into_inner().last().map(|p| p.as_str());
                arg_tuple = args.next().map(|p| p.as_str());
            }
            Rule::fn_res => {
                debug_assert!(res.is_none());
                res = Some(pair.as_str());
            }
            _ => {}
        }
    }
    Ok(ClosureSig {
        sig: format!(
            "{} -> {}",
            arg_tuple.expect("missing arg"),
            res.expect("missing res")
        ),
        closure_trait,
    })
}

#[derive(Debug, Hash)]
pub struct ClosureSig {
    sig: String,
    closure_trait: Option<ClosureTrait>,
}

impl ClosureSig {
    pub fn new(sig: &str, demangled_name: &str) -> Result<Self, failure::Error> {
        Ok(ClosureSig {
            sig: clean(sig)?,
            closure_trait: ClosureTrait::from_string(demangled_name),
        })
    }
}

#[derive(Debug, Hash)]
pub enum ClosureTrait {
    FnOnce,
    FnMut,
    Fn,
}

impl ClosureTrait {
    fn from_rule(rule: Rule) -> Self {
        match rule {
            Rule::trait_fn => ClosureTrait::Fn,
            Rule::trait_fnmut => ClosureTrait::FnMut,
            Rule::trait_fnonce => ClosureTrait::FnOnce,
            _ => unreachable!(),
        }
    }

    pub fn from_string(s: &str) -> Option<Self> {
        if s.starts_with("core::ops::function::FnOnce") {
            Some(ClosureTrait::FnOnce)
        } else if s.starts_with("core::ops::function::FnMut") {
            Some(ClosureTrait::FnMut)
        } else if s.starts_with("core::ops::function::Fn") {
            Some(ClosureTrait::Fn)
        } else {
            None
        }
    }

    fn is_subtrait_of(&self, other: &Self) -> bool {
        match other {
            ClosureTrait::FnOnce => true,
            ClosureTrait::FnMut => match self {
                ClosureTrait::FnOnce => false,
                _ => true,
            },
            ClosureTrait::Fn => match self {
                ClosureTrait::Fn => true,
                _ => false,
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Rule, Sig};
    use pest::Parser;

    #[test]
    fn caller() {
        let mut ps = Sig::parse(
            Rule::rust_sig,
            r#"extern \\22rust-call\\22 fn(&dyn for<\'r> core::ops::Fn(&\'r mut u32) -> i16, (&mut u32,)) -> i16"#,
        )
        .unwrap().next().unwrap().into_inner();
        let _ = ps.next();
        let mut args = ps.next().unwrap().into_inner();
        assert_eq!(args.clone().count(), 2);

        let arg1 = args.next().unwrap().into_inner().next().unwrap();
        println!("arg1 matched {:?}", arg1.as_rule());
        assert_eq!(arg1.as_rule(), Rule::closure_trait_arg1);

        let arg2 = args.next().unwrap().into_inner().next().unwrap();
        println!("arg2 matched {:?}", arg2.as_rule());
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
