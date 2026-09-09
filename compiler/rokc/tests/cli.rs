//! CLI behavior (spec 901 / 902 / 905): spawn the built `rokc` on
//! scratch package directories. Tests that build native code skip
//! without the LLVM toolchain (see `common::setup`).

mod common;

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use common::{Env, ROKC, setup};

fn workspace() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// A fresh scratch directory per test.
fn scratch(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rokc-cli-{}-{name}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir
}

/// `rokc <args>` in `cwd`, with the repo's library and (when given) the
/// freshly built runtime.
fn rokc(env: Option<&Env>, cwd: &Path, args: &[&str]) -> Output {
    let mut cmd = Command::new(ROKC);
    cmd.current_dir(cwd).env("ROK_HOME", workspace()).args(args);
    if let Some(env) = env {
        cmd.arg("--rokr").arg(&env.rokr);
    }
    cmd.output().unwrap()
}

fn text(b: &[u8]) -> String {
    String::from_utf8_lossy(b).into_owned()
}

#[track_caller]
fn assert_exit(out: &Output, code: i32) {
    assert_eq!(
        out.status.code(),
        Some(code),
        "stdout: {}\nstderr: {}",
        text(&out.stdout),
        text(&out.stderr)
    );
}

#[test]
fn new_bin_package_runs_from_its_directory() {
    let Some(env) = setup() else { return };
    let dir = scratch("bin");
    assert_exit(&rokc(None, &dir, &["new", "app"]), 0);
    assert!(dir.join("app/main.rok").is_file());
    // `rokc new` refuses an existing directory.
    assert_exit(&rokc(None, &dir, &["new", "app"]), 1);

    let app = dir.join("app");
    let out = rokc(Some(&env), &app, &["run"]);
    assert_exit(&out, 0);
    assert_eq!(text(&out.stdout), "Hello, world!\n");
    assert!(text(&out.stderr).contains("Compiling app"));

    // A file inside the package builds the package (902.2), and `-q`
    // silences progress.
    fs::create_dir_all(app.join("util")).unwrap();
    fs::write(app.join("util/x.rok"), "fn unused() {}\n").unwrap();
    let out = rokc(Some(&env), &dir, &["-q", "build", "app/util/x.rok"]);
    assert_exit(&out, 0);
    assert!(out.stderr.is_empty(), "{}", text(&out.stderr));
    assert!(app.join("target/debug/app").is_file());

    assert_exit(&rokc(None, &dir, &["--cwd=app", "clean"]), 0);
    assert!(!app.join("target").exists());
}

#[test]
fn lib_package_builds_archive_and_runs_tests() {
    let Some(env) = setup() else { return };
    let dir = scratch("lib");
    assert_exit(&rokc(None, &dir, &["new", "--lib", "mylib"]), 0);
    let lib = dir.join("mylib");

    assert_exit(&rokc(Some(&env), &dir, &["build", "mylib"]), 0);
    assert!(lib.join("target/debug/libmylib.a").is_file());
    assert!(lib.join("target/debug/mylib.o").is_file());
    // A library has no entry point.
    assert_exit(&rokc(Some(&env), &dir, &["run", "mylib"]), 1);

    let out = rokc(Some(&env), &lib, &["test"]);
    assert_exit(&out, 0);
    let stdout = text(&out.stdout);
    assert!(stdout.contains("test adds ... ok"), "{stdout}");
    assert!(stdout.contains("1 passed; 0 failed"), "{stdout}");

    let mut src = fs::read_to_string(lib.join("lib.rok")).unwrap();
    src.push_str(
        "\n#[cfg(test)]\nmod tests {\n    #[test]\n    fn boom() {\n        \
         println(\"from boom\");\n        panic(\"boom\");\n    }\n}\n",
    );
    fs::write(lib.join("lib.rok"), src).unwrap();
    let out = rokc(Some(&env), &lib, &["test"]);
    assert_exit(&out, 1);
    let stdout = text(&out.stdout);
    assert!(stdout.contains("test tests::boom ... FAILED"), "{stdout}");
    assert!(stdout.contains("from boom"), "{stdout}");
    assert!(stdout.contains("1 passed; 1 failed"), "{stdout}");

    // Filter (a lone non-path argument), regex anchors included.
    let out = rokc(Some(&env), &lib, &["test", "^add"]);
    assert_exit(&out, 0);
    assert!(text(&out.stdout).contains("1 passed; 0 failed; 1 filtered out"));

    // `#[test]` functions are not part of a normal build (6.2.5).
    assert_exit(&rokc(Some(&env), &lib, &["build"]), 0);
}

#[test]
fn lone_file_is_an_anonymous_package() {
    let Some(env) = setup() else { return };
    let dir = scratch("anon");
    fs::write(dir.join("hello.rok"), "println(\"hi\");\n").unwrap();
    let out = rokc(Some(&env), &dir, &["run", "hello.rok"]);
    assert_exit(&out, 0);
    assert_eq!(text(&out.stdout), "hi\n");
    // `run` of a lone file leaves no target/ behind; `build` uses one.
    assert!(!dir.join("target").exists());
    assert_exit(&rokc(Some(&env), &dir, &["build", "hello.rok"]), 0);
    assert!(dir.join("target/debug/hello").is_file());

    // Spec 4.16.8: no file submodules.
    fs::write(dir.join("m.rok"), "fn f() {}\n").unwrap();
    fs::write(dir.join("sub.rok"), "mod m;\nprintln(\"x\");\n").unwrap();
    let out = rokc(Some(&env), &dir, &["build", "sub.rok"]);
    assert_exit(&out, 1);
    assert!(
        text(&out.stderr).contains("4.16.8"),
        "{}",
        text(&out.stderr)
    );

    // A directory without main.rok / lib.rok is not a package.
    assert_exit(&rokc(Some(&env), &dir, &["build"]), 1);
}

#[test]
fn json_and_colored_diagnostics() {
    let Some(env) = setup() else { return };
    let dir = scratch("diag");
    fs::write(dir.join("bad.rok"), "let x: i32 = nope;\n").unwrap();
    let out = rokc(
        Some(&env),
        &dir,
        &["build", "--message-format=json", "bad.rok"],
    );
    assert_exit(&out, 1);
    let stdout = text(&out.stdout);
    let line = stdout.lines().next().unwrap_or_default();
    assert!(
        line.starts_with("{\"type\":\"error\",\"code\":\"E"),
        "{stdout}"
    );
    assert!(line.contains("\"file_name\":\"bad.rok\""), "{line}");
    assert!(line.contains("\"line_start\":1"), "{line}");

    let out = rokc(Some(&env), &dir, &["--color=always", "build", "bad.rok"]);
    assert!(text(&out.stderr).contains("\x1b[1;31merror\x1b[0m"));
    let out = rokc(Some(&env), &dir, &["--color=never", "build", "bad.rok"]);
    assert!(!text(&out.stderr).contains('\x1b'));
}

#[test]
fn fmt_check_and_rewrite() {
    let dir = scratch("fmt");
    let messy = "fn f() {\n  // keep me\n      let x = 1;   \n\n\n  x;\n}\n";
    let clean = "fn f() {\n    // keep me\n    let x = 1;\n\n    x;\n}\n";
    fs::create_dir_all(dir.join("target")).unwrap();
    fs::write(dir.join("a.rok"), messy).unwrap();
    fs::write(dir.join("target/skip.rok"), messy).unwrap();

    let out = rokc(None, &dir, &["fmt", "--check"]);
    assert_exit(&out, 1);
    assert!(text(&out.stdout).contains("a.rok"));
    assert_eq!(fs::read_to_string(dir.join("a.rok")).unwrap(), messy);

    assert_exit(&rokc(None, &dir, &["fmt"]), 0);
    assert_eq!(fs::read_to_string(dir.join("a.rok")).unwrap(), clean);
    assert_eq!(
        fs::read_to_string(dir.join("target/skip.rok")).unwrap(),
        messy
    );
    assert_exit(&rokc(None, &dir, &["fmt", "--check", "a.rok"]), 0);
}

#[test]
fn demangle_and_usage_errors() {
    let dir = scratch("misc");
    let out = rokc(
        None,
        &dir,
        &["demangle", "_Y3f8a1c2b_std_vec_push_a7c91d8e44b2f190"],
    );
    assert_exit(&out, 0);
    assert_eq!(
        text(&out.stdout),
        "package:  3f8a1c2b\npath:     rok::std::vec\nname:     push\n\
         generics: a7c91d8e44b2f190 (type tuple hash)\n"
    );
    assert_exit(&rokc(None, &dir, &["demangle", "_ZN3foo"]), 1);
    assert_exit(&rokc(None, &dir, &["build", "--bogus"]), 2);
    assert_exit(&rokc(None, &dir, &["frobnicate"]), 2);
    assert_exit(&rokc(None, &dir, &["--version"]), 0);
}

#[test]
fn extern_dependencies_are_top_level_names() {
    let Some(env) = setup() else { return };
    let dir = scratch("extern");
    // `greet` (a library with a submodule and a `pkg::` import) and
    // `app`, which uses it from its root and from a submodule.
    fs::create_dir_all(dir.join("greet")).unwrap();
    fs::write(
        dir.join("greet/lib.rok"),
        "pub mod words;\nuse pkg::words::hello;\n\
         pub fn greet(n: i32) -> i32 { return hello() + n; }\n",
    )
    .unwrap();
    fs::write(
        dir.join("greet/words.rok"),
        "pub fn hello() -> i32 { return 40; }\n",
    )
    .unwrap();
    fs::create_dir_all(dir.join("app")).unwrap();
    fs::write(
        dir.join("app/main.rok"),
        "mod sub;\nuse greet::greet;\nprintln(f\"{greet(1)} {sub::two()}\");\n",
    )
    .unwrap();
    fs::write(
        dir.join("app/sub.rok"),
        "use greet::words::hello;\npub fn two() -> i32 { return hello() + 2; }\n",
    )
    .unwrap();
    let out = rokc(Some(&env), &dir, &["run", "app", "--extern", "greet=greet"]);
    assert_exit(&out, 0);
    assert_eq!(text(&out.stdout), "41 42\n");
    // `--extern=name=path/lib.rok` works too; a missing prebuilt one fails.
    let out = rokc(
        Some(&env),
        &dir,
        &["build", "--release", "app", "--extern=greet=greet/lib.rok"],
    );
    assert_exit(&out, 0);
    assert!(dir.join("app/target/release/app").is_file());
    assert_exit(&rokc(None, &dir, &["build", "app", "--extern", "g=x.a"]), 1);
    // Without it, `greet` is unknown.
    assert_exit(&rokc(Some(&env), &dir, &["check", "app"]), 1);
}

#[test]
fn extern_dependency_is_a_package_boundary() {
    let Some(env) = setup() else { return };
    let dir = scratch("extern-boundary");
    // `pkg::` inside `dep` is `dep`; `dep::..` expression paths work in a
    // submodule; `pub(pkg)` / private items of `dep` stay inside it.
    fs::create_dir_all(dir.join("dep")).unwrap();
    fs::write(
        dir.join("dep/lib.rok"),
        "pub mod words;\nfn secret() -> i32 { return 1; }\n\
         pub(pkg) fn internal() -> i32 { return 2; }\n\
         pub fn via_pkg() -> i32 { return pkg::words::deep() + secret(); }\n",
    )
    .unwrap();
    fs::write(
        dir.join("dep/words.rok"),
        "pub fn hello() -> i32 { return 40; }\n\
         pub fn deep() -> i32 { return pkg::internal() * 10; }\n",
    )
    .unwrap();
    fs::create_dir_all(dir.join("app")).unwrap();
    fs::write(
        dir.join("app/main.rok"),
        "mod sub;\nfn internal() -> i32 { return 7; }\n\
         println(f\"{sub::two()} {dep::via_pkg()} {pkg::internal()}\");\n",
    )
    .unwrap();
    fs::write(
        dir.join("app/sub.rok"),
        "pub fn two() -> i32 { return dep::words::hello() + 2; }\n",
    )
    .unwrap();
    let out = rokc(Some(&env), &dir, &["run", "app", "--extern", "dep=dep"]);
    assert_exit(&out, 0);
    assert_eq!(text(&out.stdout), "42 21 7\n");

    fs::create_dir_all(dir.join("bad")).unwrap();
    fs::write(
        dir.join("bad/main.rok"),
        "println(f\"{dep::secret()} {dep::internal()}\");\n",
    )
    .unwrap();
    let out = rokc(None, &dir, &["check", "bad", "--extern", "dep=dep"]);
    assert_exit(&out, 1);
    let err = text(&out.stderr);
    assert!(err.contains("`dep::secret` is private"), "{err}");
    assert!(err.contains("`dep::internal` is `pub(pkg)`"), "{err}");

    // A user module may not take a dependency's name.
    fs::create_dir_all(dir.join("clash")).unwrap();
    fs::write(
        dir.join("clash/main.rok"),
        "mod dep;\nprintln(f\"{dep::own()}\");\n",
    )
    .unwrap();
    fs::write(
        dir.join("clash/dep.rok"),
        "pub fn own() -> i32 { return 3; }\n",
    )
    .unwrap();
    let out = rokc(None, &dir, &["check", "clash", "--extern", "dep=dep"]);
    assert_exit(&out, 1);
    assert!(
        text(&out.stderr).contains("module `dep` has the name of the dependency `dep`"),
        "{}",
        text(&out.stderr)
    );
}

/// A library built once (`lib<name>.a` + `<name>.rhir`, spec 904) and
/// linked prebuilt: its concrete code comes from the archive, its
/// generics are instantiated by the user, `any` values (a thrown error,
/// a trait object) cross the boundary both ways, and a lazy static is
/// one static. `rhir-text` / `inspect` show the interface.
#[test]
fn prebuilt_dependency_is_linked_and_instantiated() {
    let Some(env) = setup() else { return };
    let dir = scratch("prebuilt");
    fs::create_dir_all(dir.join("geo")).unwrap();
    fs::write(
        dir.join("geo/lib.rok"),
        "pub mod shapes;\n\
         static COUNT: Atomic<i32> = Atomic::new(0);\n\
         pub fn bump() -> i32 { return COUNT.fetch_add(1) + 1; }\n\
         pub struct Bad { pub at: i32; }\n\
         impl Display for Bad { fn display(self) -> str { return f\"bad {self.at}\"; } }\n\
         impl Debug for Bad { fn debug(self) -> str { return self.display(); } }\n\
         impl Error for Bad {}\n\
         pub fn check(x: i32) throws -> i32 { if x < 0 { throw Bad { at: x }; } return x * 2; }\n\
         pub struct Stack<T> { items: List<T>; }\n\
         impl<T> Stack<T> {\n\
             pub fn new() -> Stack<T> { return Stack { items: List::new() }; }\n\
             pub fn push(self, v: T) { self.items.push(v); bump(); }\n\
             pub fn len(self) -> usize { return self.items.len(); }\n\
         }\n\
         pub fn largest(xs: List<any shapes::Shape>) -> i32 {\n\
             let best = 0;\n\
             for s in xs { if s.area() > best { best = s.area(); } }\n\
             return best;\n\
         }\n",
    )
    .unwrap();
    fs::write(
        dir.join("geo/shapes.rok"),
        "pub trait Shape { fn area(self) -> i32; }\n\
         pub struct Sq { pub s: i32; }\n\
         impl Shape for Sq { fn area(self) -> i32 { return self.s * self.s; } }\n\
         pub fn sq(s: i32) -> any Shape { return Sq { s: s }; }\n",
    )
    .unwrap();
    fs::create_dir_all(dir.join("app")).unwrap();
    fs::write(
        dir.join("app/main.rok"),
        "use geo::shapes::{Shape, sq};\n\
         struct Rect { w: i32; h: i32; }\n\
         impl Shape for Rect { fn area(self) -> i32 { return self.w * self.h; } }\n\
         let st: geo::Stack<str> = geo::Stack::new();\n\
         st.push(\"a\");\n\
         println(f\"{st.len()} {geo::bump()}\");\n\
         try geo::check(-3) catch e { println(f\"caught {e}\"); };\n\
         let xs: List<any Shape> = List::new();\n\
         xs.push(Rect { w: 2, h: 9 });\n\
         xs.push(sq(4));\n\
         println(f\"{geo::largest(xs)}\");\n",
    )
    .unwrap();
    let out = rokc(Some(&env), &dir, &["build", "geo"]);
    assert_exit(&out, 0);
    let rhir = dir.join("geo/target/debug/geo.rhir");
    assert!(rhir.is_file() && dir.join("geo/target/debug/libgeo.a").is_file());
    let out = rokc(
        Some(&env),
        &dir,
        &[
            "run",
            "-q",
            "app",
            "--extern",
            &format!("geo={}", rhir.display()),
        ],
    );
    assert_exit(&out, 0);
    assert_eq!(text(&out.stdout), "1 2\ncaught bad -3\n18\n");
    // The `.a` names it too; the build used the archive, not the source.
    fs::write(dir.join("geo/lib.rok"), "this is not rok\n").unwrap();
    let out = rokc(
        Some(&env),
        &dir,
        &[
            "run",
            "-q",
            "app",
            "--extern",
            "geo=geo/target/debug/libgeo.a",
        ],
    );
    assert_exit(&out, 0);
    assert_eq!(text(&out.stdout), "1 2\ncaught bad -3\n18\n");

    // The interface: concrete bodies cut, generic ones kept.
    let out = rokc(None, &dir, &["rhir-text", "geo/target/debug/geo.rhir"]);
    assert_exit(&out, 0);
    let dump = text(&out.stdout);
    assert!(dump.contains("package: geo (hash: "), "{dump}");
    assert!(dump.contains("pub fn bump() -> i32 ;"), "{dump}");
    assert!(
        dump.contains("pub fn new() -> Stack<T> { return Stack"),
        "{dump}"
    );
    let out = rokc(None, &dir, &["inspect", "geo/target/debug/libgeo.a"]);
    assert_exit(&out, 0);
    let info = text(&out.stdout);
    for want in [
        "Package: geo\n",
        "RHIR version: 1\n",
        "Exports:\n",
        "  pub fn check(x: i32) throws -> i32\n",
        "Generic items (RHIR):\n  pub struct Stack<T>\n",
        "Concrete .o files:\n  geo.o (",
    ] {
        assert!(info.contains(want), "{want:?} in\n{info}");
    }
}

/// A RHIR from another format version or compiler, or built under
/// another name, is refused with a "rebuild" message.
#[test]
fn stale_rhir_is_rejected() {
    let Some(env) = setup() else { return };
    let dir = scratch("stale-rhir");
    fs::create_dir_all(dir.join("dep")).unwrap();
    fs::write(
        dir.join("dep/lib.rok"),
        "pub fn one() -> i32 { return 1; }\n",
    )
    .unwrap();
    fs::create_dir_all(dir.join("app")).unwrap();
    fs::write(dir.join("app/main.rok"), "println(f\"{dep::one()}\");\n").unwrap();
    assert_exit(&rokc(Some(&env), &dir, &["build", "dep"]), 0);
    let rhir = dir.join("dep/target/debug/dep.rhir");
    let ext = format!("dep={}", rhir.display());
    let out = rokc(Some(&env), &dir, &["run", "-q", "app", "--extern", &ext]);
    assert_exit(&out, 0);
    assert_eq!(text(&out.stdout), "1\n");

    let other = format!("other={}", rhir.display());
    let out = rokc(Some(&env), &dir, &["check", "app", "--extern", &other]);
    assert_exit(&out, 1);
    assert!(
        text(&out.stderr).contains("built as `dep`"),
        "{}",
        text(&out.stderr)
    );

    let good = fs::read(&rhir).unwrap();
    let mut bad = good.clone();
    bad[4] = 99; // format version
    fs::write(&rhir, &bad).unwrap();
    let out = rokc(Some(&env), &dir, &["check", "app", "--extern", &ext]);
    assert_exit(&out, 1);
    let err = text(&out.stderr);
    assert!(
        err.contains("RHIR format version 99") && err.contains("rebuild"),
        "{err}"
    );

    // Another compiler's: the producer string (after the 16-byte
    // header and its length byte) differs.
    let mut bad = good;
    bad[17 + 5] ^= 1; // inside "rokc 0.."
    fs::write(&rhir, &bad).unwrap();
    let out = rokc(Some(&env), &dir, &["check", "app", "--extern", &ext]);
    assert_exit(&out, 1);
    let err = text(&out.stderr);
    assert!(
        err.contains("was built by") && err.contains("rebuild"),
        "{err}"
    );
}

/// Library bodies nothing reaches are skipped by default;
/// `ROK_EAGER_LIBRARY` lowers (so type-checks) every one of them.
#[test]
fn eager_library_checks_every_body() {
    let dir = scratch("eager-lib");
    fs::write(dir.join("main.rok"), "fn main() {}\n").unwrap();
    let out = Command::new(ROKC)
        .current_dir(&dir)
        .env("ROK_HOME", workspace())
        .env("ROK_EAGER_LIBRARY", "1")
        .args(["check", "main.rok"])
        .output()
        .unwrap();
    assert_exit(&out, 0);
}

#[test]
fn init_makes_an_existing_directory_a_package() {
    let dir = scratch("init");
    assert_exit(&rokc(None, &dir, &["init", "--lib"]), 0);
    assert!(dir.join("lib.rok").is_file());
    assert_exit(&rokc(None, &dir, &["init"]), 1);
}
