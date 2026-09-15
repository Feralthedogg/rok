//! Build script of the runtime crates: what `target_feature = "atomics"`
//! would say on wasm32, which stable Rust does not let `cfg` see.
//! `rok_wasi_threads`: wasi-threads (`wasm32-wasip1-threads`); `rok_solo`:
//! wasm32 without threads.

fn main() {
    println!("cargo::rustc-check-cfg=cfg(rok_solo, rok_wasi_threads)");
    let target = std::env::var("TARGET").unwrap_or_default();
    if target == "wasm32-wasip1-threads" {
        println!("cargo::rustc-cfg=rok_wasi_threads");
    } else if target.starts_with("wasm32-") {
        println!("cargo::rustc-cfg=rok_solo");
    }
}
