//! `rokls`: the rok language server on stdio, the same as `rok lsp`
//! (with the project's dependencies).

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("-V" | "--version") => println!("rokls {}", rok::VERSION_LINE),
        Some("-h" | "--help") => print!(
            "usage: rokls [rok options]\n\nThe rok language server on stdin / stdout (LSP), \
             with the dependencies of the\nproject it starts in; the same as `rok lsp`. Editors \
             start it.\n"
        ),
        _ => {
            let args = std::iter::once("lsp".to_owned()).chain(args);
            std::process::exit(rok::main_with(args.collect()));
        }
    }
}
