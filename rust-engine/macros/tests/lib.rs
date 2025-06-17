use hax_rust_engine_macros::*;

#[pretty_tmpl('$')]
fn f() {
    let x = 3;
    r#"hello ${x + 3} hello"#
}
