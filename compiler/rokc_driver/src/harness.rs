//! `rokc test` harness (spec 901 `rokc test`, 6.2.5 `#[test]`): collect
//! the user package's `#[test]` functions and replace the entry point
//! with a generated `main` that runs the test named by `argv[1]`. The
//! runner spawns the binary once per test, so a panic (exit 101) or an
//! escaping error (exit 1) fails only that test.

use rokc_ast::{Item, ThrowsKind};
use rokc_diagnostic::{ErrorKind, RokDiagnostic};
use rokc_lexer::Lexer;
use rokc_parser::{ExtOps, parse_program_ext};

/// Whether `attrs` carries `#[test]`.
pub fn is_test(attrs: &[rokc_ast::Attribute]) -> bool {
    attrs
        .iter()
        .any(|a| a.path.len() == 1 && a.path[0] == "test")
}

/// Turn the user items into a test program; returns the test names
/// (`::`-qualified, in source order).
pub fn install(items: &mut Vec<Item>, ext: &ExtOps, diags: &mut Vec<RokDiagnostic>) -> Vec<String> {
    let mut tests = Vec::new();
    for item in items.iter_mut() {
        let Item::Fn(f) = item else { continue };
        if !is_test(&f.attrs) {
            continue;
        }
        if !f.params.is_empty() || !f.generics.params.is_empty() {
            diags.push(
                RokDiagnostic::error(
                    ErrorKind::Type,
                    format!(
                        "`#[test] fn {}` must take no parameters or generics",
                        f.name
                    ),
                )
                .with_span(f.span, ""),
            );
            continue;
        }
        // The generated `main` calls it from the root module.
        f.vis = rokc_core::Visibility::Pub;
        tests.push((f.name.clone(), !matches!(f.throws, ThrowsKind::None)));
    }
    // The package's own entry point is replaced (top-level statements
    // were already dropped by the caller).
    items.retain(|i| !matches!(i, Item::Fn(f) if f.name == "main"));

    let throws = tests.iter().any(|(_, t)| *t);
    let mut src = String::from(
        "extern \"C\" { fn rok_os_arg(i: usize) -> str; }\n\
         fn main() ",
    );
    if throws {
        src.push_str("throws ");
    }
    src.push_str("{\n    let name = unsafe { rok_os_arg(1usize) };\n");
    for (name, throws) in &tests {
        let call = if *throws { "try " } else { "" };
        src.push_str(&format!(
            "    if name == \"{name}\" {{ {call}{name}(); return; }}\n"
        ));
    }
    src.push_str("    panic(\"rokc test: unknown test name\");\n}\n");

    let (tokens, mut d) = Lexer::new(&src, "<test harness>").lex_all();
    diags.append(&mut d);
    let (program, mut d) = parse_program_ext(&tokens, "<test harness>", ext);
    diags.append(&mut d);
    items.extend(program.items);
    tests.into_iter().map(|(n, _)| n).collect()
}
