use hax_rust_engine_macros::*;

#[pretty_tmpl('$')]
fn f() {
    let x = 3;
    r#"hel$nest[3]{lo ${x + 3} hel}lo"#
}
