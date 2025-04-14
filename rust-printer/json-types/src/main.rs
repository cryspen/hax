#![feature(rustc_private)]

fn main() {
    let mut schema = schemars::schema_for!((rust_printer::ast::Item,));
    schema.schema.metadata.get_or_insert_default().id = Some("unknown".into());
    serde_json::to_writer(std::io::stdout(), &schema).unwrap();
}
