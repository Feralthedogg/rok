//! `rokc test` harness (spec 901 `rokc test`, 6.2.5 `#[test]`): collect
//! the user package's `#[test]` functions and replace the entry point
//! with a generated `main` that runs the test named by `argv[1]`. The
//! runner spawns the binary once per test, so a panic (exit 101) or an
//! escaping error (exit 1) fails only that test.
//!
//! `rokc bench` uses the same scheme over `#[bench]` functions; its
//! `main` times rounds of calls (see `bench_main`).

use rokc_ast::{Item, ThrowsKind};
use rokc_diagnostic::{ErrorKind, RokDiagnostic};
use rokc_lexer::Lexer;
use rokc_parser::{ExtOps, parse_program_ext};

/// Whether `attrs` carries `#[test]`.
pub fn is_test(attrs: &[rokc_ast::Attribute]) -> bool {
    has_attr(attrs, "test")
}

/// Whether `attrs` carries `#[name]` (one path segment).
pub fn has_attr(attrs: &[rokc_ast::Attribute], name: &str) -> bool {
    attrs.iter().any(|a| a.path.len() == 1 && a.path[0] == name)
}

/// Turn the user items into a test program (`bench`: a benchmark
/// program over the `#[bench]` functions); returns the test / bench names
/// (`::`-qualified, in source order).
pub fn install(
    items: &mut Vec<(String, Item)>,
    ext: &ExtOps,
    diags: &mut Vec<RokDiagnostic>,
    bench: bool,
) -> Vec<String> {
    let attr = if bench { "bench" } else { "test" };
    let mut tests = Vec::new();
    for (module, item) in items.iter() {
        let Item::Fn(f) = item else { continue };
        if !has_attr(&f.attrs, attr) {
            continue;
        }
        if !f.params.is_empty() || !f.generics.params.is_empty() {
            diags.push(RokDiagnostic::error(
                ErrorKind::Type,
                f.span,
                format!(
                    "`#[{attr}] fn {}` must take no parameters or generics",
                    f.name
                ),
            ));
            continue;
        }
        let name = if module.is_empty() {
            f.name.clone()
        } else {
            format!("{module}::{}", f.name)
        };
        tests.push((name, !matches!(f.throws, ThrowsKind::None)));
    }
    // The package's own entry point is replaced (top-level statements
    // were already dropped by the caller).
    items.retain(|(m, i)| !(m.is_empty() && matches!(i, Item::Fn(f) if f.name == "main")));

    let src = if bench {
        bench_main(&tests)
    } else {
        test_main(&tests)
    };
    let (tokens, mut d) = Lexer::new(&src, "<test harness>").lex_all();
    diags.append(&mut d);
    let (program, mut d) = parse_program_ext(&tokens, "<test harness>", ext);
    diags.append(&mut d);
    items.extend(program.items.into_iter().map(|i| (String::new(), i)));
    tests.into_iter().map(|(n, _)| n).collect()
}

/// `main` running the test named by `argv[1]` once.
fn test_main(tests: &[(String, bool)]) -> String {
    let throws = tests.iter().any(|(_, t)| *t);
    let mut src = String::from("fn main() ");
    if throws {
        src.push_str("throws ");
    }
    src.push_str("{\n    let name = rok::std::env::args()[1];\n");
    for (name, throws) in tests {
        let call = if *throws { "try " } else { "" };
        src.push_str(&format!(
            "    if name == \"{name}\" {{ {call}{name}(); return; }}\n"
        ));
    }
    src.push_str("    panic(\"rokc test: unknown test name\");\n}\n");
    src
}

/// `main` for `rokc bench`: `argv` = `name iters samples`. Runs `samples`
/// timed rounds of `iters` calls of the bench `name`, printing each
/// round's elapsed nanoseconds as a `#rokbench <ns>` line (the runner
/// ignores the bench's own output).
fn bench_main(benches: &[(String, bool)]) -> String {
    let mut src = String::from(
        "extern \"C\" { fn rok_time_now_ns() -> i64; }\n\
         fn main() {\n\
         \x20   let argv = rok::std::env::args();\n\
         \x20   let name = argv[1];\n\
         \x20   let iters: i64 = try! argv[2].parse();\n\
         \x20   let samples: i64 = try! argv[3].parse();\n\
         \x20   let s = 0i64;\n\
         \x20   while s < samples {\n\
         \x20       let i = 0i64;\n\
         \x20       let t0 = unsafe { rok_time_now_ns() };\n",
    );
    for (k, (name, throws)) in benches.iter().enumerate() {
        let call = if *throws { "try! " } else { "" };
        let kw = if k == 0 { "if" } else { "else if" };
        src.push_str(&format!(
            "        {kw} name == \"{name}\" {{ while i < iters {{ {call}{name}(); i += 1i64; }} }}\n"
        ));
    }
    if !benches.is_empty() {
        src.push_str("        else ");
    }
    src.push_str(
        "{ panic(\"rokc bench: unknown bench name\"); }\n\
         \x20       let t1 = unsafe { rok_time_now_ns() };\n\
         \x20       println(f\"#rokbench {t1 - t0}\");\n\
         \x20       s += 1i64;\n\
         \x20   }\n\
         }\n",
    );
    src
}
