//! `rok`: see the library.

fn main() {
    let default_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        default_hook(info);
        eprintln!("rok: internal error");
        std::process::exit(101);
    }));
    std::process::exit(rok::main_with(std::env::args().skip(1).collect()));
}
