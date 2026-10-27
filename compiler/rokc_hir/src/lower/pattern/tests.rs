use std::cell::Cell;
use std::hint::black_box;
use std::time::{Duration, Instant};

use super::*;

#[derive(Clone, Copy, PartialEq)]
enum Backend {
    Auto,
    Matrix,
    Sat,
    EmptyBudget,
}

thread_local! {
    static BACKEND: Cell<Backend> = const { Cell::new(Backend::Auto) };
    static SAT_QUERIES: Cell<usize> = const { Cell::new(0) };
    static FALLBACKS: Cell<usize> = const { Cell::new(0) };
}

pub(super) fn record_query() {
    SAT_QUERIES.set(SAT_QUERIES.get() + 1);
}

pub(super) fn empty_budget() -> bool {
    BACKEND.get() == Backend::EmptyBudget
}

pub(super) fn record_fallback() {
    FALLBACKS.set(FALLBACKS.get() + 1);
}

pub(super) fn matrix_only() -> bool {
    BACKEND.get() == Backend::Matrix
}

pub(super) fn sat_only() -> bool {
    matches!(BACKEND.get(), Backend::Sat | Backend::EmptyBudget)
}

fn with_backend<T>(backend: Backend, f: impl FnOnce() -> T) -> T {
    struct Restore(Backend);
    impl Drop for Restore {
        fn drop(&mut self) {
            BACKEND.set(self.0);
        }
    }
    let _restore = Restore(BACKEND.replace(backend));
    f()
}

const fn boolean(b: bool) -> Pat {
    Pat::C(Ctor::Bool(b), Vec::new())
}

const fn tuple(parts: Vec<Pat>) -> Pat {
    Pat::C(Ctor::Single, parts)
}

fn matches(p: &Pat, bits: &[bool]) -> bool {
    match p {
        Pat::Wild => true,
        Pat::C(Ctor::Bool(b), _) => bits == [*b],
        Pat::C(Ctor::Single, parts) => parts.iter().zip(bits).all(|(p, b)| matches(p, &[*b])),
        Pat::Or(alts) => alts.iter().any(|p| matches(p, bits)),
        Pat::C(..) => panic!("not a Boolean product"),
    }
}

fn next(seed: &mut u64) -> u64 {
    *seed ^= *seed << 13;
    *seed ^= *seed >> 7;
    *seed ^= *seed << 17;
    *seed
}

fn random_cube(seed: &mut u64, n: usize) -> Pat {
    let parts = (0..n)
        .map(|_| match next(seed) % 5 {
            0 => Pat::Wild,
            1 => boolean(false),
            2 => boolean(true),
            3 => Pat::Or(vec![boolean(false), boolean(true)]),
            _ => Pat::Or(vec![boolean(true), boolean(true)]),
        })
        .collect();
    tuple(parts)
}

fn random_pattern(seed: &mut u64, n: usize) -> Pat {
    let p = random_cube(seed, n);
    match next(seed) % 4 {
        0 => Pat::Or(vec![p, random_cube(seed, n)]),
        1 => Pat::Or(vec![p, Pat::Or(Vec::new())]),
        _ => p,
    }
}

#[test]
fn sat_agrees_with_exhaustive_boolean_assignments() {
    let mut seed = 0x71ae_b9c3_50d2_8f64;
    for n in 1..=6 {
        let ty = HirTy::Tuple(vec![HirTy::Prim(PrimTy::Bool); n]);
        for _ in 0..200 {
            let mut sat = sat::Checker::new(&ty).unwrap();
            let mut earlier = Vec::new();
            for _ in 0..8 {
                let p = random_pattern(&mut seed, n);
                let expected = (0..1usize << n).any(|mask| {
                    let bits: Vec<_> = (0..n).map(|i| mask & (1 << i) != 0).collect();
                    matches(&p, &bits) && !earlier.iter().any(|p| matches(p, &bits))
                });
                assert_eq!(sat.useful(&p), Some(expected), "{p:?}, rows={earlier:?}");
                // Guarded arms do not exclude assignments.
                if next(&mut seed) % 3 != 0 {
                    sat.exclude(&p).unwrap();
                    earlier.push(p);
                }
            }
            let expected = (0..1usize << n).any(|mask| {
                let bits: Vec<_> = (0..n).map(|i| mask & (1 << i) != 0).collect();
                !earlier.iter().any(|p| matches(p, &bits))
            });
            assert_eq!(sat.useful(&Pat::Wild), Some(expected));
        }
    }
}

fn program(source: &str) -> Program {
    let (tokens, lex) = rokc_lexer::Lexer::new(source, "sat-test.rok").lex_all();
    assert!(lex.is_empty(), "{lex:?}");
    let (p, errors) = rokc_parser::parse_program(&tokens, "sat-test.rok");
    assert!(errors.is_empty(), "{errors:?}\n{source}");
    p
}

fn diagnostics(p: &Program, backend: Backend) -> String {
    with_backend(backend, || format!("{:?}", lower(p).diagnostics))
}

fn lower(p: &Program) -> HirModule {
    let input = crate::HirInput {
        item_modules: vec![String::new(); p.items.len()],
        check_library: true,
        ..crate::HirInput::default()
    };
    crate::lower_full(
        p.clone(),
        &PrecTable::new(),
        &[],
        &HashMap::new(),
        &[],
        &input,
        &rokc_diagnostic::SourceMap::new(),
    )
}

fn source(n: usize, patterns: &[String], guards: bool) -> String {
    let ty = vec!["bool"; n].join(", ");
    let arms = patterns
        .iter()
        .enumerate()
        .map(|(i, p)| {
            format!(
                "{p}{} => {i},",
                if guards && i % 3 == 0 { " if g" } else { "" }
            )
        })
        .collect::<Vec<_>>()
        .join("\n");
    format!("fn f(p: ({ty}), g: bool) -> i32 {{ match p {{ {arms} }} }}")
}

fn pat_text(p: &Pat) -> String {
    match p {
        Pat::Wild => "_".to_owned(),
        Pat::C(Ctor::Bool(b), _) => b.to_string(),
        Pat::C(Ctor::Single, parts) => format!(
            "({})",
            parts.iter().map(pat_text).collect::<Vec<_>>().join(", ")
        ),
        Pat::Or(alts) => alts
            .iter()
            .filter(|p| !matches!(p, Pat::Or(alts) if alts.is_empty()))
            .map(pat_text)
            .collect::<Vec<_>>()
            .join(" | "),
        Pat::C(..) => panic!("not a Boolean product"),
    }
}

#[test]
fn sat_and_matrix_report_identical_diagnostics() {
    let mut seed = 0x2b35_f1dc_a842_9e76;
    for n in 2..=6 {
        for _ in 0..40 {
            let patterns: Vec<_> = (0..8)
                .map(|_| {
                    let p = random_pattern(&mut seed, n);
                    pat_text(&p)
                })
                .collect();
            let p = program(&source(n, &patterns, next(&mut seed) % 2 == 0));
            assert_eq!(
                diagnostics(&p, Backend::Sat),
                diagnostics(&p, Backend::Matrix)
            );
            assert_eq!(
                diagnostics(&p, Backend::Auto),
                diagnostics(&p, Backend::Matrix)
            );
        }
    }
    for text in [
        "fn f(p: ((bool, bool), bool)) -> i32 { match p { ((true, _), _) => 1, ((false, true), _) => 2 } }",
        "struct S { a: bool; b: bool; } fn f(p: S) -> i32 { match p { S { a: true, .. } => 1 } }",
        "enum E { A, B(bool) } fn f(p: E) -> i32 { match p { E::A => 0, E::B(true) => 1 } }",
        "fn f(p: i32) -> i32 { match p { 1..=3 => 0, 2 => 1, _ => 2 } }",
    ] {
        let p = program(text);
        assert_eq!(
            diagnostics(&p, Backend::Sat),
            diagnostics(&p, Backend::Matrix)
        );
    }
}

#[test]
fn unsupported_types_and_work_limits_request_fallback() {
    assert!(sat::Checker::new(&HirTy::Prim(PrimTy::I32)).is_none());
    let ty = HirTy::Tuple(vec![HirTy::Prim(PrimTy::Bool); 513]);
    assert!(sat::Checker::new(&ty).is_none());
    let mut checker = sat::Checker::new(&HirTy::Prim(PrimTy::Bool)).unwrap();
    checker.exclude(&boolean(true)).unwrap();
    assert_eq!(checker.useful(&Pat::Wild), Some(true));
    assert_eq!(checker.useful(&boolean(true)), Some(false));
}

fn workloads() -> Vec<(String, String)> {
    let mut out = vec![
        ("scalar-bool".to_owned(), "fn f(p: bool) -> i32 { match p { true => 1, false => 0 } }".to_owned()),
        ("tiny-catchall".to_owned(), source(2, &["_".to_owned()], false)),
        ("mixed-tuple".to_owned(), "fn f(p: (bool, i32)) -> i32 { match p { (true, _) => 1, (false, _) => 0 } }".to_owned()),
        ("enum".to_owned(), "enum E { A, B(bool) } fn f(p: E) -> i32 { match p { E::A => 0, E::B(true) => 1, E::B(false) => 2 } }".to_owned()),
    ];
    for n in [2, 4, 8, 16, 32] {
        let patterns: Vec<_> = (0..=n)
            .map(|i| {
                let parts = (0..n).map(|j| match j.cmp(&i) {
                    std::cmp::Ordering::Less => "false",
                    std::cmp::Ordering::Equal => "true",
                    std::cmp::Ordering::Greater => "_",
                });
                format!("({})", parts.collect::<Vec<_>>().join(", "))
            })
            .collect();
        out.push((format!("chain-{n}"), source(n, &patterns, false)));
    }
    for n in [4, 8, 12, 16] {
        let patterns = [format!("({})", vec!["false | true"; n].join(", "))];
        out.push((format!("or-cover-{n}"), source(n, &patterns, false)));
    }
    let mut parts = vec!["false | true"; 16];
    parts[15] = "true";
    let hole = [format!("({})", parts.join(", "))];
    out.push(("or-hole-16".to_owned(), source(16, &hole, false)));
    let mut parts = vec!["_"; 16];
    parts[0] = "true";
    let missing = [format!("({})", parts.join(", "))];
    out.push(("missing-16".to_owned(), source(16, &missing, false)));
    let guarded = vec![format!("({})", vec!["false | true"; 16].join(", "))];
    out.push(("guarded-16".to_owned(), source(16, &guarded, true)));
    let mut seed = 0x2718_2818_2845_9045;
    for n in [8, 16, 32] {
        let patterns: Vec<_> = (0..n * 2)
            .map(|_| {
                let mut parts = vec!["_"; n];
                for _ in 0..3 {
                    let j = next(&mut seed) as usize % n;
                    parts[j] = if next(&mut seed) % 2 == 0 {
                        "false"
                    } else {
                        "true"
                    };
                }
                format!("({})", parts.join(", "))
            })
            .collect();
        out.push((format!("sparse-{n}"), source(n, &patterns, false)));
    }
    out
}

#[test]
fn diagnostics_exercise_bodies_witnesses_and_budget_fallback() {
    let p = program("fn f(p: (bool, bool)) -> i32 { match p { (true, _) => 1 } }");
    let expected = diagnostics(&p, Backend::Matrix);
    assert!(expected.contains("non-exhaustive match"), "{expected}");
    assert!(expected.contains("(false, false)"), "{expected}");
    SAT_QUERIES.set(0);
    assert_eq!(diagnostics(&p, Backend::Sat), expected);
    assert!(SAT_QUERIES.get() > 0);
    FALLBACKS.set(0);
    assert_eq!(diagnostics(&p, Backend::EmptyBudget), expected);
    assert!(FALLBACKS.get() > 0);
    let p = program(
        "fn f(p: (bool, bool)) -> i32 { match p { (true, _) => 1, (false, _) => 2, (true, true) => 3 } }",
    );
    let expected = diagnostics(&p, Backend::Matrix);
    assert!(expected.contains("unreachable match arm 3"), "{expected}");
    assert_eq!(diagnostics(&p, Backend::Sat), expected);
    assert_eq!(diagnostics(&p, Backend::EmptyBudget), expected);
    let p = program(&source(
        8,
        &[format!("({})", ["false | true"; 8].join(", "))],
        false,
    ));
    let expected = diagnostics(&p, Backend::Matrix);
    assert_eq!(expected, "[]");
    SAT_QUERIES.set(0);
    assert_eq!(diagnostics(&p, Backend::Auto), expected);
    assert!(SAT_QUERIES.get() > 0);
}

/// Run with `cargo test -p rokc_hir --release pattern_benchmark -- --ignored --nocapture`.
#[test]
#[ignore = "release comparison benchmark"]
fn pattern_benchmark() {
    let filter = std::env::var("ROK_PATTERN_BENCH_FILTER").unwrap_or_default();
    let mode = std::env::var("ROK_PATTERN_BENCH_MODE").unwrap_or_default();
    for (name, text) in workloads().into_iter().filter(|(n, _)| n.contains(&filter)) {
        let p = program(&text);
        if mode.is_empty() {
            let expected = diagnostics(&p, Backend::Matrix);
            assert_eq!(diagnostics(&p, Backend::Sat), expected, "{name}");
            assert_eq!(diagnostics(&p, Backend::Auto), expected, "{name}");
        }
        let modes: Vec<_> = [
            ("matrix", Backend::Matrix),
            ("sat", Backend::Sat),
            ("auto", Backend::Auto),
        ]
        .into_iter()
        .filter(|(label, _)| mode.is_empty() || mode == *label)
        .collect();
        let run = |backend| with_backend(backend, || black_box(lower(black_box(&p))));
        let mut iterations = Vec::new();
        for &(label, backend) in &modes {
            SAT_QUERIES.set(0);
            FALLBACKS.set(0);
            let start = Instant::now();
            let result = black_box(run(backend));
            assert!(!result.functions.is_empty() || !result.diagnostics.is_empty());
            let one = start.elapsed();
            let iters = (Duration::from_millis(30).as_nanos() / one.as_nanos().max(1))
                .clamp(1, 1000) as u32;
            iterations.push(iters);
            println!(
                "PATTERN_PATH,{name},{label},{},{},{}",
                SAT_QUERIES.get(),
                FALLBACKS.get(),
                result.diagnostics.len()
            );
        }
        let mut samples = vec![Vec::new(); modes.len()];
        // Alternate order to reduce warm-cache and thermal bias.
        for round in 0..7 {
            for j in 0..modes.len() {
                let i = if round % 2 == 0 {
                    j
                } else {
                    modes.len() - 1 - j
                };
                let start = Instant::now();
                for _ in 0..iterations[i] {
                    black_box(run(modes[i].1));
                }
                samples[i].push(start.elapsed().as_nanos() / u128::from(iterations[i]));
            }
        }
        for (i, (label, _)) in modes.iter().enumerate() {
            samples[i].sort_unstable();
            println!(
                "PATTERN_BENCH,{name},{label},{},{},{},{}",
                iterations[i], samples[i][3], samples[i][0], samples[i][6]
            );
        }
    }
}
