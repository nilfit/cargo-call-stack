#![allow(warnings)]

use std::collections::HashMap;

use pest::Parser;
use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "ir.pest"]
struct Ir;

pub fn parse(ll: &str) -> Result<Vec<Define>, failure::Error> {
    let file = Ir::parse(Rule::file, ll)?.next().expect("unreachable");

    // first pass: look for !rust_name metadata which has the form `!42 = !{!"const Trait::method"}`
    // and !rust_sig which has the form `!42 = !{!"fn(type) -> type"}`
    let mut metadata_names = HashMap::new();
    let mut metadata = HashMap::new();
    for item in file
        .clone()
        .into_inner()
        // skip SOI / EOI
        .filter(|p| p.as_rule() == Rule::item)
        .map(|p| p.into_inner().next().expect("unreachable"))
        .filter(|p| p.as_rule() == Rule::metadata_alias)
    {
        let alias = item.into_inner().next().expect("unreachable");

        if alias.as_rule() == Rule::metadata_alias_string {
            let mut pairs = alias.into_inner();

            let first = pairs.next().expect("unreachable");
            debug_assert_eq!(first.as_rule(), Rule::metadata_number);

            let second = pairs.next().expect("unreachable");
            debug_assert_eq!(second.as_rule(), Rule::string);

            let string = second.as_str();
            debug_assert!(string.starts_with('"'));
            debug_assert!(string.ends_with('"'));

            // XXX the compiler will eventually stop emitting this leading "const "
            if string.starts_with("\"const ") {
                let number = first.as_str();
                debug_assert!(number.starts_with("!"));

                let number = number[1..].parse::<u64>().expect("unreachable");

                metadata_names.insert(number, &string["\"const ".len()..string.len() - 1]);
            } else {
                let number = first.as_str();
                debug_assert!(number.starts_with("!"));

                let number = number[1..].parse::<u64>().expect("unreachable");

                metadata.insert(number, &string[1..string.len() - 1]);
            }
        }
    }

    // second pass: parse all the `define` items
    let mut defines = vec![];
    for item in file
        .into_inner()
        // skip SOI / EOI
        .filter(|p| p.as_rule() == Rule::item)
        .map(|p| p.into_inner().next().expect("unreachable"))
        .filter(|p| p.as_rule() == Rule::define)
    {
        let item_span = item.as_span();
        let mut name = None;
        let mut sig = None;
        let mut calls = vec![];
        for pair in item.into_inner() {
            match pair.as_rule() {
                Rule::metadata_list_whitespace => {
                    for md in pair.into_inner() {
                        debug_assert!(md.as_rule() == Rule::metadata);
                        let mut pairs = md.into_inner();
                        let md_ident = pairs.next().expect("unreachable");
                        if md_ident.as_str() == "!rust_sig" {
                            let md_number = pairs.next().expect("unreachable");
                            debug_assert_eq!(md_number.as_rule(), Rule::metadata_number);

                            let idx = md_number.as_str()[1..].parse::<u64>().expect("unreachable");

                            sig = metadata.get(&idx).cloned().map(String::from);
                        }
                    }
                }
                Rule::symbol => {
                    assert!(name.is_none());

                    name = Some(symbol_to_string(pair.as_str()));
                }
                Rule::instruction => {
                    // Rule = (assign | maybe_call) ~ metadata_list
                    let mut pairs = pair.into_inner();
                    // assign | maybe_call
                    let mut first = pairs.next().unwrap();
                    let meta_list_opt = pairs.next();

                    // Rule = maybe_call
                    if first.as_rule() == Rule::assign {
                        first = first.into_inner().next().unwrap();
                    }

                    // Rule = call_asm | call_direct | call_indirect | not_call
                    let pair = first.into_inner().next().unwrap();
                    match pair.as_rule() {
                        Rule::call_asm => {
                            let expr = pair
                                .into_inner()
                                .filter(|p| p.as_rule() == Rule::asm_expr)
                                .next()
                                .expect("unreachable")
                                .into_inner()
                                .filter(|p| p.as_rule() == Rule::string)
                                .next()
                                .expect("unreachable")
                                .as_str();

                            debug_assert!(expr.starts_with('"'));
                            debug_assert!(expr.ends_with('"'));

                            calls.push(Call::Asm {
                                expr: expr[1..expr.len() - 1].to_owned(),
                            });
                        }
                        Rule::call_direct => {
                            let symbol = pair
                                .into_inner()
                                .filter(|p| p.as_rule() == Rule::id_global)
                                .next()
                                .expect("unreachable")
                                .as_str();

                            // these intrinsics don't use the stack
                            if symbol.starts_with("@llvm.dbg.")
                                || symbol.starts_with("@llvm.lifetime.")
                                || symbol == "@llvm.assume"
                                || symbol == "@llvm.trap"
                            {
                                continue;
                            }
                            let callee = symbol_to_string(symbol);

                            calls.push(Call::Direct { callee });
                        }
                        Rule::call_indirect => {
                            let mut path = None;
                            let mut sig = None;

                            let span = pair.as_span();

                            for pair in meta_list_opt.unwrap().into_inner() {
                                debug_assert_eq!(pair.as_rule(), Rule::metadata);

                                let mut pairs = pair.into_inner();

                                let first = pairs.next().expect("unreachable");
                                debug_assert_eq!(first.as_rule(), Rule::metadata_identifier);

                                match first.as_str() {
                                    "!rust_name" => {
                                        let second = pairs.next().expect("unreachable");
                                        debug_assert_eq!(second.as_rule(), Rule::metadata_number);

                                        let idx = second.as_str()[1..]
                                            .parse::<u64>()
                                            .expect("unreachable");

                                        // NOTE `None` means that this is a function pointer
                                        path = metadata_names.get(&idx).cloned();
                                    }
                                    "!rust_sig" => {
                                        let second = pairs.next().expect("unreachable");
                                        debug_assert_eq!(second.as_rule(), Rule::metadata_number);

                                        let idx = second.as_str()[1..]
                                            .parse::<u64>()
                                            .expect("unreachable");

                                        // This should be present for all calls
                                        sig = metadata.get(&idx).cloned();
                                    }
                                    _ => {}
                                }
                            }

                            let er = format!("missing sig metadata for indirect call: {:?}", span);
                            let sig = String::from(sig.expect(&er));

                            if let Some(path) = path {
                                let mut parts = path.rsplitn(2, "::");

                                let method = parts.next().expect("unreachable").to_owned();
                                let name = parts.next().expect("unreachable").to_owned();

                                calls.push(Call::Trait { name, method, sig });
                            } else {
                                calls.push(Call::Fn { sig });
                            }
                        }
                        Rule::not_call => {
                            // Not a function call
                        }
                        _ => unreachable!(),
                    }
                }
                _ => {}
            }
        }

        let er = format!("missing sig in define: {:?}", item_span);
        defines.push(Define {
            name: name.unwrap(),
            calls,
            sig: sig.expect(&er),
        })
    }

    Ok(defines)
}

#[derive(Debug)]
pub struct Define {
    name: String,
    calls: Vec<Call>,
    sig: String,
}

impl Define {
    pub fn calls(&self) -> &[Call] {
        &self.calls
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn sig(&self) -> &str {
        &self.sig
    }
}

#[derive(Debug)]
pub enum Call {
    // TODO add `expression: String`
    Asm {
        expr: String,
    },
    Direct {
        callee: String,
    },
    // function pointer
    Fn {
        sig: String,
    },
    Trait {
        name: String,
        method: String,
        sig: String,
    },
}

fn symbol_to_string(mut symbol: &str) -> String {
    debug_assert!(symbol.starts_with("@"));

    // drop `@`
    symbol = &symbol[1..];

    if symbol.starts_with('"') {
        // drop surrounding double quotes
        symbol[1..symbol.len() - 1].to_owned()
    } else {
        symbol.to_owned()
    }
}

#[cfg(test)]
mod tests {
    use std::fs;

    use pest::Parser;

    use super::{Ir, Rule};

    #[test]
    fn call_asm() {
        let mut pairs = Ir::parse(
            Rule::call_asm,
            r#"tail call void asm sideeffect "BKPT 1", ""() #2, !srcloc !804"#,
        )
        .unwrap();

        let asm_expr = pairs
            .next()
            .unwrap()
            .into_inner()
            .filter(|p| p.as_rule() == Rule::asm_expr)
            .next()
            .unwrap();
        assert_eq!(
            asm_expr.into_inner().skip(1).next().unwrap().as_str(),
            "\"BKPT 1\""
        );
        Ir::parse(
                Rule::call_asm,
                r#"tail call void asm sideeffect "", "r,r,r,r,r,r"(i32 0, i32 1, i32 2, i32 3, i32 4, i32 5) #2, !dbg !83, !srcloc !85"#,
            )
            .unwrap();
    }

    #[test]
    fn call_direct() {
        Ir::parse(
            Rule::call_direct,
            r#"call fastcc void @_ZN4core9panicking9panic_fmt17h8e7152a45a601b4bE()"#,
        )
        .unwrap();

        Ir::parse(
            Rule::call_direct,
            r#"tail call fastcc zeroext i1 @_ZN20cortex_m_semihosting6export11hstdout_str17hf865bdec51fe6423E([0 x i8]* noalias nonnull readonly bitcast (<{ [5 x i8] }>* @1 to [0 x i8]*))"#,
        )
            .unwrap();
    }

    #[test]
    fn call_indirect() {
        Ir::parse(
            Rule::call_indirect,
            r#"tail call void %3({}* nonnull %0) #2"#,
        )
        .unwrap();

        let mut top_pairs = Ir::parse(
            Rule::instruction,
            r#"tail call i32 %0() #0, !dbg !323, !rust !324"#,
        )
        .unwrap();

        let mut pairs = top_pairs.next().unwrap().into_inner();
        let _ = pairs.next().unwrap();
        let mut meta_list = pairs.next().unwrap().into_inner();

        let first = meta_list.next().unwrap();
        assert_eq!(first.as_rule(), Rule::metadata);
        assert_eq!(first.as_str(), "!dbg !323");

        {
            let mut pairs = first.into_inner();
            let first = pairs.next().unwrap();
            assert_eq!(first.as_rule(), Rule::metadata_identifier);
            assert_eq!(first.as_str(), "!dbg");

            let second = pairs.next().unwrap();
            assert_eq!(second.as_rule(), Rule::metadata_number);
            assert_eq!(second.as_str(), "!323");
        }

        let second = meta_list.next().unwrap();
        assert_eq!(second.as_rule(), Rule::metadata);
        assert_eq!(second.as_str(), "!rust !324");

        {
            let mut pairs = second.into_inner();
            let first = pairs.next().unwrap();
            assert_eq!(first.as_rule(), Rule::metadata_identifier);
            assert_eq!(first.as_str(), "!rust");

            let second = pairs.next().unwrap();
            assert_eq!(second.as_rule(), Rule::metadata_number);
            assert_eq!(second.as_str(), "!324");
        }

        assert!(pairs.next().is_none());
    }

    #[test]
    fn comment() {
        Ir::parse(Rule::comment, "; core::ptr::drop_in_place\n").unwrap();
    }

    #[test]
    fn constant() {
        Ir::parse(
            Rule::constant,
            r#"@__RESET_VECTOR = local_unnamed_addr constant <{ i8*, [0 x i8] }> <{ i8* bitcast (void ()* @Reset to i8*), [0 x i8] zeroinitializer }>, section ".vector_table.reset_vector", align 4"#,
        )
            .unwrap();
    }

    #[test]
    fn define() {
        let mut pairs = Ir::parse(
            Rule::define,
            r#"define void @_ZN3bar3foo17he50f1da75616209aE() unnamed_addr #0 {
start: ; comment
  ret void
}"#,
        )
        .unwrap();

        assert!(pairs
            .next()
            .unwrap()
            .into_inner()
            .any(|pair| pair.as_rule() == Rule::symbol
                && pair.as_str() == "@_ZN3bar3foo17he50f1da75616209aE"));

        Ir::parse(
            Rule::define,
            r#"define internal fastcc void @_ZN4core9panicking5panic17h58fdea4fa7a9abc8E({ [0 x i32], { [0 x i8]*, i32 }, [0 x i32], { [0 x i8]*, i32 }, [0 x i32], i32, [0 x i32], i32, [0 x i32] }* noalias nocapture readonly dereferenceable(24)) unnamed_addr #10 {
  unreachable
}"#,
        )
            .unwrap();
    }

    #[test]
    fn files() -> Result<(), failure::Error> {
        for e in fs::read_dir("tests")? {
            let p = e?.path();

            super::parse(&fs::read_to_string(p)?)?;
        }

        Ok(())
    }

    #[test]
    fn global() {
        Ir::parse(
            Rule::global,
            r#"@0 = private unnamed_addr global <{ [0 x i8] }> zeroinitializer, align 1"#,
        )
        .unwrap();
    }

    #[test]
    fn label() {
        Ir::parse(
            Rule::label,
            "_ZN8cortex_m9interrupt4free17h5f184a4c1aab19e3E.exit: ; preds = %start, %bb6.i",
        )
        .unwrap();

        Ir::parse(
            Rule::label,
            "\"_ZN45_$LT$heapless..vec..Vec$LT$T$C$$u20$N$GT$$GT$4push17hb1ae5cec1b70e16aE.exit\":",
        )
        .unwrap();
    }

    #[test]
    fn metadata_identifier() {
        Ir::parse(Rule::metadata_identifier, "!rust").unwrap();
    }

    #[test]
    fn metadata_number() {
        Ir::parse(Rule::metadata_number, "!0").unwrap();
    }

    #[test]
    fn metadata_alias_string() {
        let mut pairs = Ir::parse(
            Rule::metadata_alias_string,
            r#"!337 = !{!"const Trait::m"}"#,
        )
        .unwrap()
        .next()
        .unwrap()
        .into_inner();

        let first = pairs.next().unwrap();
        assert_eq!(first.as_rule(), Rule::metadata_number);
        assert_eq!(first.as_str(), "!337");

        let second = pairs.next().unwrap();
        assert_eq!(second.as_rule(), Rule::string);
        assert_eq!(second.as_str(), "\"const Trait::m\"");
    }

    #[test]
    fn source_filename() {
        Ir::parse(
            Rule::source_filename,
            r#"source_filename = "schedule.7pp9b8v3-cgu.0""#,
        )
        .unwrap();
    }

    #[test]
    fn symbol() {
        Ir::parse(
            Rule::symbol,
            r#"@"_ZN35_$LT$app..X$u20$as$u20$app..Foo$GT$3bar17hb1828ca2da3f44fcE""#,
        )
        .unwrap();
    }

    #[test]
    fn target_datalayout() {
        Ir::parse(
            Rule::target_datalayout,
            r#"target datalayout = "e-m:e-p:32:32-i64:64-v128:64:128-a:0:32-n32-S64"#,
        )
        .unwrap();
    }

    #[test]
    fn target_triple() {
        Ir::parse(
            Rule::target_triple,
            r#"target triple = "thumbv7m-none-unknown-eabi"#,
        )
        .unwrap();
    }

    #[test]
    fn type_alias() {
        Ir::parse(Rule::type_alias, r#"%X = type {}"#).unwrap();
    }

    #[test]
    fn ty_metadata_number() {
        Ir::parse(Rule::ty_metadata, "metadata !968").unwrap();
    }

    #[test]
    fn ty_metadata_node() {
        Ir::parse(Rule::ty_metadata, "metadata !DIExpression()").unwrap();
    }

    #[test]
    fn call_indirect_meta() {
        Ir::parse(
            Rule::instruction,
            "%1 = tail call i16 %0(i32 3) #3, !dbg !360, !rust_sig !203, !rust_name !361",
        )
        .unwrap();
    }

    #[test]
    fn call_direct_meta() {
        Ir::parse(
            Rule::instruction,
            "tail call void @__pre_init(), !dbg !261, !rust_sig !262, !rust_name !263",
        )
        .unwrap();
    }
}
