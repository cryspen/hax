use hax_frontend_exporter as frontend;
use rust_printer::ast::*;
use serde::Deserialize;

fn module_path(global_id: &GlobalId) -> Vec<String> {
    let global_id = global_id.to_string();
    let chunks = global_id.split("::").collect::<Vec<_>>();
    let Some((_def_name, [_krate, module_path @ ..])) = chunks.split_last() else {
        unimplemented!()
    };
    module_path.iter().map(ToString::to_string).collect()
}

fn print_items(items: Vec<Item>) {
    let items: Vec<_> = items
        .into_iter()
        .filter(|item| !matches!(item.kind, ItemKind::Error(_)))
        .collect();
    let modules: Vec<Vec<String>> = items.iter().map(|item| module_path(&item.ident)).collect();
    let modules: Vec<Vec<&str>> = modules
        .iter()
        .map(|chunks| chunks.iter().map(|s| s.as_str()).collect::<Vec<_>>())
        .collect();
    let modules: Vec<_> = modules
        .into_iter()
        .map(|path| (1..=path.len()).map(move |i| path[..i].to_vec()))
        .flatten()
        .collect();
    let modules: Vec<_> = modules
        .iter()
        .filter_map(|path| path.split_last())
        .collect();

    #[derive(Clone)]
    struct ModPrinter<'a> {
        current_path: Vec<&'a str>,
        modules: &'a [(&'a &'a str, &'a [&'a str])],
        items: &'a [Item],
    }

    let printer = ModPrinter {
        modules: &modules,
        items: &items,
        current_path: vec![],
    };

    impl<'a> ModPrinter<'a> {
        fn with_current_path(&self, current_path: Vec<&'a str>) -> Self {
            ModPrinter {
                current_path,
                items: self.items,
                modules: self.modules,
            }
        }
        fn print(&'a self) {
            println!("#![feature(panic_internals)]\n");
            for item in self.items {
                let mod_path = module_path(&item.ident);
                if mod_path == self.current_path {
                    // TODO: we dropped the Rust printer, for now, just print the debug of `item`
                    println!("{:#?}", item);
                }
            }
            for (name, path) in self
                .modules
                .iter()
                .filter(|(_, path)| path == &&self.current_path[..])
            {
                println!("pub mod {name} {{");
                let mut current_path = path.to_vec();
                current_path.push(name);
                self.with_current_path(current_path).print();
                println!("}}");
            }
        }
    }

    printer.print();
}

#[derive(Deserialize)]
#[serde(untagged)]
enum Input {
    Thir(Vec<frontend::Item<frontend::ThirBody>>),
    Ast(Vec<rust_printer::ast::Item>),
}

fn main() {
    print_items(
        match serde_json::from_reader(std::io::stdin()).expect("Valid JSON on stdin") {
            Input::Thir(items) => items
                .iter()
                .map(rust_printer::import::translate_item)
                .collect(),
            Input::Ast(items) => items,
        },
    )
}
