// `ROK_TARGET_HOST`: the target this crate is built for, the default
// `--target`.

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!(
        "cargo:rustc-env=ROK_TARGET_HOST={}",
        std::env::var("TARGET").unwrap_or_default()
    );
}
