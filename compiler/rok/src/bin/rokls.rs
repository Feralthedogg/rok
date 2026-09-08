//! `rokls`: the rok language server on stdio, the same as `rok lsp`
//! (with the project's dependencies).

fn main() {
    let args = std::iter::once("lsp".to_owned()).chain(std::env::args().skip(1));
    std::process::exit(rok::main_with(args.collect()));
}
