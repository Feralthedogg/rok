//! Native-code behavior checked against the platform: the C ABI (spec
//! 8.6) against clang-compiled C, the runtime's stack-overflow report,
//! and `-g` DWARF. Skips without the LLVM toolchain (`common::setup`).

mod common;

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use common::{Env, ROKC, setup};

fn scratch(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rokc-native-{}-{name}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir
}

fn text(b: &[u8]) -> String {
    String::from_utf8_lossy(b).into_owned()
}

/// `rokc build <src> <extra..>` with the harness library and runtime.
fn build(env: &Env, src: &Path, extra: &[&str]) -> Output {
    Command::new(ROKC)
        .arg("-q")
        .arg("build")
        .arg(src)
        .arg("--bootstrap")
        .arg(&env.bootstrap)
        .arg("--rokr")
        .arg(&env.rokr)
        .args(std::env::var("ROK_TEST_OPT").ok().filter(|o| !o.is_empty()))
        .args(extra)
        .output()
        .unwrap()
}

#[track_caller]
fn ok(out: &Output) {
    assert!(
        out.status.success(),
        "status {:?}\nstdout: {}\nstderr: {}",
        out.status,
        text(&out.stdout),
        text(&out.stderr)
    );
}

const C_SIDE: &str = r"
#include <stdarg.h>
typedef struct { float x, y, z; } V3;
typedef struct { double a, b, c, d; } D4;
typedef struct { long a, b, c; } Big;
typedef struct { signed char a; short b; } Small;
typedef struct { long a; double b; } Mix;
typedef struct { int a, b, c; } I3;
V3 v3_scale(V3 v, float k) { V3 r = { v.x * k, v.y * k, v.z * k }; return r; }
double d4_sum(D4 d) { return d.a + d.b + d.c + d.d; }
Big big_make(long a) { Big b = { a, a * 2, a * 3 }; return b; }
long big_sum(Big b) { return b.a + b.b + b.c; }
Small small_inc(Small s) { s.a += 1; s.b += 1; return s; }
Mix mix_twice(Mix m) { m.a *= 2; m.b *= 2; return m; }
int i3_sum(I3 s) { return s.a + s.b + s.c; }
long many(long a, long b, long c, long d, long e, I3 s, long f) {
    return a + b + c + d + e + s.a + s.b + s.c + f;
}
int sx(signed char c, unsigned short u) { return c * 100000 + u; }
long vsum(int n, ...) {
    va_list ap; va_start(ap, n); long t = 0;
    for (int i = 0; i < n; i++) t += va_arg(ap, long);
    va_end(ap); return t;
}
typedef struct { int q, r; } DT;
DT dt_div(int n, int d) { DT x = { n / d, n % d }; return x; }
int via(DT (*f)(int, int)) { DT d = f(9, 4); return d.q * 10 + d.r; }
double vmix(int n, ...) {
    va_list ap; va_start(ap, n); double t = 0;
    for (int i = 0; i < n; i++) { t += va_arg(ap, int); t += va_arg(ap, double); }
    va_end(ap); return t;
}
int cb_v3(V3 (*f)(V3, float)) { V3 v = { 1, 2, 3 }; V3 r = f(v, 3.0f); return (int)(r.x + r.y + r.z); }
long cb_big(Big (*f)(Big)) { Big b = { 1, 2, 3 }; Big r = f(b); return r.a * 100 + r.b * 10 + r.c; }
double cb_d4(double (*f)(D4)) { D4 d = { 1, 2, 3, 4 }; return f(d); }
Small cb_small(Small (*f)(Small)) { Small s = { 4, 5 }; return f(s); }
Mix rok_mix(Mix m);
double call_rok_mix(void) { Mix m = { 3, 0.5 }; Mix r = rok_mix(m); return r.a + r.b; }
Big rev_c(Big b) { Big r = { b.c, b.b, b.a }; return r; }
V3 (*get_v3_scale(void))(V3, float) { return v3_scale; }
Big (*get_rev(void))(Big) { return rev_c; }
long cb_big2(Big (*f)(Big)) { return cb_big(f); }
";

const ROK_SIDE: &str = r#"
struct V3 { x: f32; y: f32; z: f32; }
struct D4 { a: f64; b: f64; c: f64; d: f64; }
struct Big { a: i64; b: i64; c: i64; }
struct Small { a: i8; b: i16; }
struct Mix { a: i64; b: f64; }
struct I3 { a: i32; b: i32; c: i32; }
struct DT { q: i32; r: i32; }

extern "C" {
    fn v3_scale(v: V3, k: f32) -> V3;
    fn d4_sum(d: D4) -> f64;
    fn big_make(a: i64) -> Big;
    fn big_sum(b: Big) -> i64;
    fn small_inc(s: Small) -> Small;
    fn mix_twice(m: Mix) -> Mix;
    fn i3_sum(s: I3) -> i32;
    fn many(a: i64, b: i64, c: i64, d: i64, e: i64, s: I3, f: i64) -> i64;
    fn sx(c: i8, u: u16) -> i32;
    fn vsum(n: i32, ...) -> i64;
    fn vmix(n: i32, ...) -> f64;
    fn dt_div(n: i32, d: i32) -> DT;
    fn via(f: unsafe fn(i32, i32) -> DT) -> i32;
    fn printf(fmt: str, ...) -> i32;
    fn cb_v3(f: fn(V3, f32) -> V3) -> i32;
    fn cb_big(f: fn(Big) -> Big) -> i64;
    fn cb_d4(f: fn(D4) -> f64) -> f64;
    fn cb_small(f: fn(Small) -> Small) -> Small;
    fn call_rok_mix() -> f64;
    // C function pointers as values (spec 5.9.4).
    fn get_v3_scale() -> extern "C" fn(V3, f32) -> V3;
    fn get_rev() -> extern "C" fn(Big) -> Big;
    fn cb_big2(f: extern "C" fn(Big) -> Big) -> i64;
}

// C calls these (spec 5.9.10): aggregates the C way both ways.
extern "C" fn scale_v3(v: V3, k: f32) -> V3 { V3 { x: v.x * k, y: v.y * k, z: v.z * k } }
extern "C" fn rev_big(b: Big) -> Big { Big { a: b.c, b: b.b, c: b.a } }
extern "C" fn sum_d4(d: D4) -> f64 { d.a + d.b + d.c + d.d }
extern "C" fn neg_small(s: Small) -> Small { Small { a: -s.a, b: -s.b } }
#[export_name("rok_mix")]
extern "C" fn mix_rok(m: Mix) -> Mix { Mix { a: m.a + 1, b: m.b * 2.0 } }

fn main() {
    unsafe {
        let v = v3_scale(V3 { x: 1.0, y: 2.0, z: 3.0 }, 2.0);
        println(f"{v.x} {v.y} {v.z}");
        println(f"{d4_sum(D4 { a: 1.0, b: 2.0, c: 3.0, d: 4.5 })}");
        let b = big_make(5);
        println(f"{b.a} {b.b} {b.c} {big_sum(b)}");
        let s = small_inc(Small { a: -3, b: 300 });
        println(f"{s.a} {s.b}");
        let m = mix_twice(Mix { a: 21, b: 1.25 });
        println(f"{m.a} {m.b}");
        println(f"{i3_sum(I3 { a: 1, b: 2, c: 3 })}");
        println(f"{many(1, 2, 3, 4, 5, I3 { a: 6, b: 7, c: 8 }, 9)}");
        let c: i8 = -5;
        let u: u16 = 65535;
        println(f"{sx(c, u)}");
        let x: i64 = 40;
        println(f"{vsum(3, x, x, 2 as i64)}");
        let small: i8 = -2;
        let half: f32 = 0.5;
        println(f"{vmix(2, small, half, true, 1.25)}");
        // A C function handed back to C as a pointer keeps its C type.
        println(f"{via(dt_div)}");
        let n = cb_small(neg_small);
        println(f"{cb_v3(scale_v3)} {cb_big(rev_big)} {cb_d4(sum_d4) as i64} {call_rok_mix() as i64} {n.a} {n.b}");
    }
    // From rok they are rok functions.
    let r = rev_big(Big { a: 7, b: 8, c: 9 });
    println(f"{r.a}{r.b}{r.c}");
    // `extern "C" fn` values: received from C, made from a rok `extern
    // "C" fn` (its C entry), called with the C ABI, handed back to C.
    let f = unsafe { get_v3_scale() };
    let w = f(V3 { x: 1.0, y: 2.0, z: 3.0 }, 2.0);
    let g: extern "C" fn(Big) -> Big = unsafe { get_rev() };
    let rb = g(Big { a: 1, b: 2, c: 3 });
    let h: extern "C" fn(Big) -> Big = rev_big;
    let rh = h(Big { a: 4, b: 5, c: 6 });
    let k: extern "C" fn(Small) -> Small | none = neg_small;
    let ks = match k { none => Small { a: 0, b: 0 }, p: extern "C" fn(Small) -> Small => p(Small { a: 1, b: 2 }) };
    println(f"{w.x} {w.y} {w.z} {rb.a}{rb.b}{rb.c} {rh.a}{rh.b}{rh.c} {ks.a} {ks.b} {unsafe { cb_big2(h) }}");
}
"#;

const OVERFLOW: &str = r#"
use rok::std::thread;

// Not a tail call, and no accumulator LLVM could turn into a loop.
fn down(n: i64) -> i64 {
    if n == 0 { return 0; }
    return down(n - 1) % 7 + 1;
}

async fn deep(n: i64) -> i64 {
    if n == 0 { return 0; }
    return (await deep(n - 1)) % 7 + 1;
}

fn main() {
    print("before\n");
    let args = rok::std::env::args();
    let mode = args[1];
    if mode == "main" {
        println(f"{down(1000000000)}");
    } else if mode == "thread" {
        let h = thread::spawn(|| down(1000000000));
        println(f"{try! h.join()}");
    } else {
        println(f"{task::block_on(deep(1000000000))}");
    }
}
"#;

/// Runaway recursion on the main thread, a spawned thread and through
/// nested `await`s: the runtime reports it (after flushing stdout) and
/// aborts, instead of a bare SIGSEGV.
#[test]
fn stack_overflow_is_reported() {
    let Some(env) = setup() else { return };
    let dir = scratch("overflow");
    fs::write(dir.join("main.rok"), OVERFLOW).unwrap();
    let exe = dir.join("out");
    let out = Command::new(ROKC)
        .args(["-q", "build"])
        .arg(dir.join("main.rok"))
        .arg("--bootstrap")
        .arg(&env.bootstrap)
        .arg("--bootstrap")
        .arg(env.workspace.join("library/std/lib.rok"))
        .arg("--rokr")
        .arg(&env.rokr)
        .args(std::env::var("ROK_TEST_OPT").ok().filter(|o| !o.is_empty()))
        .arg("-o")
        .arg(&exe)
        .output()
        .unwrap();
    ok(&out);
    for (mode, name) in [("main", "main"), ("thread", "<unnamed>"), ("async", "main")] {
        let run = Command::new(&exe).arg(mode).output().unwrap();
        let stderr = text(&run.stderr);
        assert!(!run.status.success(), "{mode}: {:?}", run.status);
        assert!(
            stderr.contains(&format!("thread '{name}' has overflowed its stack")),
            "{mode}: {stderr}"
        );
        assert_eq!(text(&run.stdout), "before\n", "{mode}");
    }
}

const DEBUGGEE: &str = "fn add(a: i32, b: i32) -> i32 {
    let s = a + b;
    let t = s * 2;
    return t;
}

fn main() {
    let x = add(3, 4);
    let p = P { x: x, y: 2.5 };
    let name = \"rok\";
    let pair = (p, [1u8, 2u8]);
    if x > 0 {
        let x = pair.1[0];
        println(f\"{pair.0.x + x as i32 - 1}\");
    }
}

struct P { x: i32; y: f64; }
";

/// `-g` (spec 9.9.6): a subprogram named by the rok path with its
/// parameters and locals, and a line table pointing into the `.rok`.
#[test]
fn debug_info_names_functions_lines_and_locals() {
    let Some(env) = setup() else { return };
    let Some(dump) = ["llvm-dwarfdump", "dwarfdump"]
        .into_iter()
        .find(|t| Command::new(t).arg("--version").output().is_ok())
    else {
        return;
    };
    let dir = scratch("debug");
    fs::write(dir.join("main.rok"), DEBUGGEE).unwrap();
    let exe = dir.join("out");
    ok(&build(
        &env,
        &dir.join("main.rok"),
        &["-g", "-o", exe.to_str().unwrap()],
    ));
    let run = Command::new(&exe).output().unwrap();
    ok(&run);
    assert_eq!(text(&run.stdout), "14\n");
    // macOS keeps DWARF in the `.dSYM` clang's dsymutil step writes.
    let dsym = dir.join("out.dSYM");
    let target = if dsym.exists() { dsym } else { exe };
    let info = Command::new(dump)
        .arg("--debug-info")
        .arg(&target)
        .output()
        .unwrap();
    let info = text(&info.stdout);
    let sub = info
        .split("DW_TAG_subprogram")
        .find(|s| s.contains("(\"add\")") && s.contains("main.rok"))
        .unwrap_or_else(|| panic!("no `add` subprogram:\n{info}"));
    assert!(sub.contains("DW_AT_decl_line\t(1)"), "{sub}");
    for var in ["(\"a\")", "(\"b\")", "(\"s\")", "(\"t\")", "\"i32\")"] {
        assert!(sub.contains(var), "`add` lacks {var}:\n{sub}");
    }
    assert!(
        info.contains("(\"main\")"),
        "no rok `main` subprogram:\n{info}"
    );
    // The shadowing `x` lives in the `if` body's lexical block.
    let main = info
        .split("DW_TAG_subprogram")
        .find(|s| s.contains("(\"main\")") && s.contains("main.rok"))
        .unwrap_or_else(|| panic!("no rok `main`:\n{info}"));
    let block = main
        .split("DW_TAG_lexical_block")
        .nth(1)
        .unwrap_or_else(|| panic!("no lexical block:\n{main}"));
    assert!(
        block.contains("(\"x\")") && block.contains("\"u8\")"),
        "{block}"
    );
    // Aggregates: a struct with its fields, `str`, a tuple, an array.
    let p = info
        .split("DW_TAG_structure_type")
        .find(|s| s.contains("DW_AT_name\t(\"P\")"))
        .unwrap_or_else(|| panic!("no `P` type:\n{info}"));
    for want in ["(\"x\")", "(\"y\")", "DW_AT_data_member_location\t(0x08)"] {
        assert!(p.contains(want), "`P` lacks {want}:\n{p}");
    }
    for want in [
        "(\"p\")",
        "(\"name\")",
        "(\"pair\")",
        "(\"str\")",
        "(\"tuple\")",
        "DW_TAG_array_type",
    ] {
        assert!(info.contains(want), "no {want}:\n{info}");
    }
    let lines = Command::new(dump)
        .arg("--debug-line")
        .arg(&target)
        .output()
        .unwrap();
    let lines = text(&lines.stdout);
    assert!(lines.contains("main.rok"), "{lines}");
    // `let t = s * 2;` (line 3) has a row.
    assert!(
        lines
            .lines()
            .any(|l| l.split_whitespace().nth(1) == Some("3")),
        "no line-3 row:\n{lines}"
    );
}

/// Aggregates by value both ways, HFAs, `sret`, register exhaustion,
/// caller-extended narrow ints and variadic promotions, against clang.
const NICHE_C: &str = r"
#include <stddef.h>
typedef long (*op)(long);
typedef struct { op f; long x; } Cb;
long twice(long x) { return 2 * x; }
op get_op(int some) { return some ? twice : NULL; }
long call_or(op f, long x, long d) { return f ? f(x) : d; }
long run_cb(Cb c) { return c.f ? c.f(c.x) : -1; }
Cb make_cb(int some) { Cb c = { some ? twice : NULL, 21 }; return c; }
op slot;
long call_slot(long x) { return slot ? slot(x) : -1; }
";

const NICHE_ROK: &str = r#"
struct Cb { f: extern "C" fn(i64) -> i64 | none; x: i64; }

extern "C" {
    fn twice(x: i64) -> i64;
    fn get_op(some: i32) -> extern "C" fn(i64) -> i64 | none;
    fn call_or(f: extern "C" fn(i64) -> i64 | none, x: i64, d: i64) -> i64;
    fn run_cb(c: Cb) -> i64;
    fn make_cb(some: i32) -> Cb;
    fn call_slot(x: i64) -> i64;
    static mut slot: extern "C" fn(i64) -> i64 | none;
}

extern "C" fn neg(x: i64) -> i64 { -x }

fn show(f: extern "C" fn(i64) -> i64 | none) -> str {
    match f { none => "none", g: extern "C" fn(i64) -> i64 => f"{g(5)}" }
}

fn widen(f: extern "C" fn(i64) -> i64 | none) -> extern "C" fn(i64) -> i64 | none | i32 { f }

fn back(v: extern "C" fn(i64) -> i64 | none | i32) -> str {
    match v { g: extern "C" fn(i64) -> i64 => f"fn {g(1)}", none => "none", i: i32 => f"i32 {i}" }
}

fn main() {
    let a = unsafe { get_op(1) };
    let z = unsafe { get_op(0) };
    println(f"{a is none} {z is none} {show(a)} {show(z)}");
    if let g: extern "C" fn(i64) -> i64 = a { println(f"if-let {g(21)}"); }
    if let g: extern "C" fn(i64) -> i64 = z { println(f"bad {g(1)}"); } else { println("if-let none"); }
    let n: extern "C" fn(i64) -> i64 | none = none;
    let p: extern "C" fn(i64) -> i64 | none = neg;
    println(f"{unsafe { call_or(n, 4, 99) }} {unsafe { call_or(p, 4, 99) }} {unsafe { call_or(a, 4, 99) }}");
    let xs: List<extern "C" fn(i64) -> i64 | none> = List::new();
    xs.push(a);
    xs.push(z);
    xs.push(p);
    for f in xs { print(f"{show(f)},"); }
    println("");
    let c = Cb { f: p, x: 7 };
    let d = Cb { f: none, x: 7 };
    let m = unsafe { make_cb(1) };
    let k = unsafe { make_cb(0) };
    println(f"{unsafe { run_cb(c) }} {unsafe { run_cb(d) }} {show(m.f)} {m.x} {show(k.f)} {unsafe { run_cb(m) }}");
    let wi: extern "C" fn(i64) -> i64 | none | i32 = 3;
    println(f"{back(widen(a))} {back(widen(z))} {back(wi)}");
    let narrow: extern "C" fn(i64) -> i64 | none = match widen(a) { i: i32 => none, g: extern "C" fn(i64) -> i64 | none => g };
    println(f"{show(narrow)}");
    let dflt: extern "C" fn(i64) -> i64 = neg;
    let h = z ?? dflt;
    let h2 = a ?? dflt;
    println(f"{h(3)} {h2(3)}");
    unsafe {
        println(f"{show(slot)} {call_slot(50)}");
        slot = neg;
        println(f"{show(slot)} {call_slot(50)}");
        slot = none;
        println(f"{slot is none} {call_slot(50)}");
    }
}
"#;

/// Spec 5.9.4 null niche: `extern "C" fn(..) | none` is one pointer,
/// null = `none`, through C arguments / results, struct fields, a
/// `List`, a `static`, widening into a tagged sum and back, and `??`.
#[test]
fn c_fn_ptr_null_niche() {
    let Some(env) = setup() else { return };
    let dir = scratch("cniche");
    fs::write(dir.join("side.c"), NICHE_C).unwrap();
    fs::write(dir.join("main.rok"), NICHE_ROK).unwrap();
    let obj = dir.join("main.o");
    ok(&build(
        &env,
        &dir.join("main.rok"),
        &["--emit=obj", "-o", obj.to_str().unwrap()],
    ));
    let exe = dir.join("out");
    ok(&Command::new("clang")
        .arg(&obj)
        .arg(dir.join("side.c"))
        .arg(&env.rokr)
        .args(["-lm", "-o"])
        .arg(&exe)
        .output()
        .unwrap());
    let run = Command::new(&exe).output().unwrap();
    ok(&run);
    assert_eq!(
        text(&run.stdout),
        "false true 10 none\nif-let 42\nif-let none\n99 -4 8\n10,none,-5,\n\
         -7 -1 10 21 none 42\nfn 2 none i32 3\n10\n-3 6\nnone -1\n-5 -50\ntrue -1\n"
    );
}

#[test]
fn c_abi_matches_clang() {
    let Some(env) = setup() else { return };
    let dir = scratch("cabi");
    fs::write(dir.join("side.c"), C_SIDE).unwrap();
    fs::write(dir.join("main.rok"), ROK_SIDE).unwrap();
    let obj = dir.join("main.o");
    ok(&build(
        &env,
        &dir.join("main.rok"),
        &["--emit=obj", "-o", obj.to_str().unwrap()],
    ));
    let exe = dir.join("out");
    ok(&Command::new("clang")
        .arg(&obj)
        .arg(dir.join("side.c"))
        .arg(&env.rokr)
        .args(["-lm", "-o"])
        .arg(&exe)
        .output()
        .unwrap());
    let run = Command::new(&exe).output().unwrap();
    ok(&run);
    assert_eq!(
        text(&run.stdout),
        "2 4 6\n10.5\n5 10 15 30\n-2 301\n42 2.5\n6\n45\n-434465\n82\n0.75\n21\n18 321 10 5 -4 -5\n987\n2 4 6 321 654 -1 -2 321\n"
    );

    // The other targets' lowering, as LLVM IR declarations (what clang
    // emits for `side.c`, modulo clang splitting a SysV two-eightbyte
    // struct into two parameters, which LLVM does the same way).
    let decls = |triple: &str| {
        let ll = dir.join(format!("{triple}.ll"));
        ok(&build(
            &env,
            &dir.join("main.rok"),
            &[
                "--emit=llvmir",
                &format!("--target={triple}"),
                "-o",
                ll.to_str().unwrap(),
            ],
        ));
        fs::read_to_string(ll).unwrap()
    };
    let x86 = decls("x86_64-unknown-linux-gnu");
    for want in [
        "declare { <2 x float>, float } @v3_scale({ <2 x float>, float }, float)",
        "declare double @d4_sum(ptr byval({ double, double, double, double }) align 8)",
        "declare void @big_make(ptr sret({ i64, i64, i64 }) align 8, i64)",
        "declare i32 @small_inc(i32)",
        "declare { i64, double } @mix_twice({ i64, double })",
        "declare i32 @i3_sum({ i64, i32 })",
        // Only one GPR left for a two-eightbyte struct: all in memory.
        "declare i64 @many(i64, i64, i64, i64, i64, ptr byval({ i32, i32, i32 }) align 8, i64)",
        "declare i32 @sx(i8 signext, i16 zeroext)",
        "declare i64 @vsum(i32, ...)",
        "call double (i32, ...) @vmix(i32 2, i32",
    ] {
        assert!(x86.contains(want), "x86_64 lacks `{want}`:\n{x86}");
    }
    // A call through an `extern "C" fn(Big) -> Big` pointer: `sret` and
    // `byval` on the call site, as on a declaration.
    assert!(
        x86.lines().any(|l| l.contains("call void %")
            && l.contains("ptr sret({ i64, i64, i64 })")
            && l.contains("ptr byval({ i64, i64, i64 })")),
        "x86_64 lacks an indirect C call with sret / byval:\n{x86}"
    );
    let a64 = decls("aarch64-unknown-linux-gnu");
    for want in [
        "declare [3 x float] @v3_scale([3 x float], float)",
        "declare double @d4_sum([4 x double])",
        "declare void @big_make(ptr sret({ i64, i64, i64 }) align 8, i64)",
        "declare i64 @big_sum(ptr)",
        "declare i32 @small_inc(i64)",
        "declare [2 x i64] @mix_twice([2 x i64])",
        "declare i64 @many(i64, i64, i64, i64, i64, [2 x i64], i64)",
    ] {
        assert!(a64.contains(want), "aarch64 lacks `{want}`:\n{a64}");
    }
}
