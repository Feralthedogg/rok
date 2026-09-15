//! CLI behavior (spec 901 / 902 / 905): spawn the built `rokc` on
//! scratch package directories. Tests that build native code skip
//! when rokc is built without LLVM (see `common::setup`).

mod common;

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use common::{Env, ROKC, assert_exit, scratch, setup, text, workspace};

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

/// `dir/name/main.rok` (or `lib.rok` with a test), as `rok new` makes it.
fn new_package(dir: &Path, name: &str, lib: bool) -> PathBuf {
    let pkg = dir.join(name);
    fs::create_dir_all(&pkg).unwrap();
    if lib {
        let src = "pub fn add(a: i32, b: i32) -> i32 {\n    return a + b;\n}\n\n#[test]\n\
                   fn adds() {\n    if add(2, 2) != 4 {\n        panic(\"add(2, 2) != 4\");\n    }\n}\n";
        fs::write(pkg.join("lib.rok"), src).unwrap();
    } else {
        fs::write(pkg.join("main.rok"), "println(\"Hello, world!\");\n").unwrap();
    }
    pkg
}

#[test]
fn new_bin_package_runs_from_its_directory() {
    let Some(env) = setup() else { return };
    let dir = scratch("bin");
    let app = new_package(&dir, "app", false);
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

/// `--emit=ast` (9.9.10): the package after meta expansion, as rok
/// source (derived impls, `if let` as `match`; no comments).
#[test]
fn emit_ast_shows_derives_and_desugaring() {
    let dir = scratch("ast");
    fs::write(
        dir.join("main.rok"),
        "// gone\n#[derive(Clone)]\nstruct P { x: i32; }\n\
         fn main() {\n    let v: i32 | none = 3;\n    if let n: i32 = v { println(f\"{n}\"); }\n}\n",
    )
    .unwrap();
    let out = rokc(None, &dir, &["build", "--emit=ast", "-o", "x.rok"]);
    assert_exit(&out, 0);
    let text = fs::read_to_string(dir.join("x.rok")).unwrap();
    assert!(
        text.contains("impl rok::core::marker::Clone for P {")
            && text.contains("return P { x: self.x.clone() };")
            && text.contains("match v {\n        n: i32 => {")
            && !text.contains("gone"),
        "{text}"
    );
}

/// 9.2.8 in a library build: every function of the package is a root
/// (even a private one nothing calls), library code it does not reach
/// is dropped.
#[test]
fn library_build_drops_code_its_package_does_not_reach() {
    let dir = scratch("libprune");
    let lib = dir.join("plib");
    fs::create_dir_all(&lib).unwrap();
    fs::write(
        lib.join("lib.rok"),
        "pub fn f() -> f64 { 2.0.sqrt() }\nfn unused_private() -> i32 { 2 }\n",
    )
    .unwrap();
    let out = rokc(None, &dir, &["emit", "plib", "--emit=mir", "-o", "p.mir"]);
    assert_exit(&out, 0);
    let mir = fs::read_to_string(dir.join("p.mir")).unwrap();
    assert!(mir.contains("fn plib::unused_private()"), "{mir}");
    assert!(mir.contains("fn plib::f()"), "{mir}");
    assert!(!mir.contains("fn rok_f64_cbrt("), "{mir}");
    assert!(mir.matches("\nfn ").count() < 40, "{mir}");
}

/// 902.16: an unchanged package is not rebuilt; a changed source, a
/// different option or a replaced output rebuilds it.
#[test]
fn unchanged_package_is_fresh() {
    let Some(env) = setup() else { return };
    let dir = scratch("fresh");
    let app = new_package(&dir, "app", false);
    let built = |args: &[&str]| {
        let out = rokc(Some(&env), &app, args);
        assert_exit(&out, 0);
        let stderr = text(&out.stderr);
        assert!(
            stderr.contains("Fresh app") != stderr.contains("Compiling app"),
            "{stderr}"
        );
        (stderr.contains("Compiling app"), text(&out.stdout))
    };
    assert!(built(&["build"]).0);
    assert_eq!(built(&["run"]), (false, "Hello, world!\n".to_owned()));
    fs::write(app.join("main.rok"), "println(\"changed\");\n").unwrap();
    assert_eq!(built(&["run"]), (true, "changed\n".to_owned()));
    assert!(!built(&["build"]).0);
    assert!(built(&["build", "-g"]).0);
    assert!(!built(&["build", "-g"]).0);
    // A file the package does not use is still one of its sources.
    fs::write(app.join("other.rok"), "fn f() {}\n").unwrap();
    assert!(built(&["build", "-g"]).0);
    fs::write(app.join("target/debug/app"), "").unwrap();
    assert!(built(&["build", "-g"]).0);
    // A `#[path]` module outside the package is a source too.
    fs::write(dir.join("shared.rok"), "pub fn v() -> i32 {\n    1\n}\n").unwrap();
    fs::write(
        app.join("main.rok"),
        "#[path(\"../shared.rok\")]\nmod shared;\n\nprintln(f\"{shared::v()}\");\n",
    )
    .unwrap();
    assert_eq!(built(&["run"]), (true, "1\n".to_owned()));
    assert_eq!(built(&["run"]), (false, "1\n".to_owned()));
    fs::write(dir.join("shared.rok"), "pub fn v() -> i32 {\n    2\n}\n").unwrap();
    assert_eq!(built(&["run"]), (true, "2\n".to_owned()));
}

/// `-vv` (909.5): the files read and the generic instances made.
#[test]
fn very_verbose_lists_files_and_instances() {
    let dir = scratch("very_verbose");
    let app = dir.join("app");
    fs::create_dir_all(&app).unwrap();
    fs::write(
        app.join("main.rok"),
        "fn id<T>(x: T) -> T {\n    x\n}\n\nprintln(f\"{id(1)}\");\n",
    )
    .unwrap();
    let out = rokc(None, &app, &["emit", "-vv", "--emit=hir"]);
    assert_exit(&out, 0);
    let stderr = text(&out.stderr);
    assert!(stderr.contains("     Reading main.rok\n"), "{stderr}");
    assert!(
        stderr.contains(" Specialized id(x: i32) -> i32\n"),
        "{stderr}"
    );
    let out = rokc(None, &app, &["emit", "-v", "--emit=hir"]);
    assert!(!text(&out.stderr).contains("Specialized"));
}

/// A nested fn's item (and symbol) name: the enclosing fn's (`Type.m`
/// for a method), `/`, its own; `/2` .. for a repeated name.
#[test]
fn nested_fn_item_names() {
    let dir = scratch("nested_fn_names");
    fs::write(
        dir.join("main.rok"),
        "struct S {}\nimpl S {\n    fn m(self) -> i32 {\n        fn h() -> i32 { 1 }\n        h()\n    }\n}\n\
         fn f() -> i32 {\n    let a = { fn g() -> i32 { 2 } g() };\n    let b = { fn g() -> i32 { 3 } g() };\n    a + b\n}\n\
         fn main() {\n    println(f\"{S {}.m() + f()}\");\n}\n",
    )
    .unwrap();
    let out = rokc(None, &dir, &["emit", "--emit=hir", "-o", "h.txt"]);
    assert_exit(&out, 0);
    let hir = fs::read_to_string(dir.join("h.txt")).unwrap();
    for f in ["fn S.m/h()", "fn f/g()", "fn f/g/2()"] {
        assert!(hir.contains(f), "{f}");
    }
}

#[test]
fn lib_package_builds_archive_and_runs_tests() {
    let Some(env) = setup() else { return };
    let dir = scratch("lib");
    let lib = new_package(&dir, "mylib", true);

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
    assert!(text(&out.stderr).contains("\x1b[1;31merror[E100]\x1b[0m"));
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

    // `.rokon` data files too: re-indented, and checked to be RokON.
    fs::write(dir.join("rok.rokon"), "Package {\n  deps: {}, // none\n}\n").unwrap();
    assert_exit(&rokc(None, &dir, &["fmt"]), 0);
    assert_eq!(
        fs::read_to_string(dir.join("rok.rokon")).unwrap(),
        "Package {\n    deps: {}, // none\n}\n"
    );
    fs::write(dir.join("bad.rokon"), "Package { name: x }\n").unwrap();
    let out = rokc(None, &dir, &["fmt", "--check"]);
    assert_exit(&out, 1);
    assert!(
        text(&out.stderr).contains("error[E002]: bare identifier `x`")
            && text(&out.stderr).contains("bad.rokon:1:17\n"),
        "{}",
        text(&out.stderr)
    );
}

/// A file saved with CRLF (spec 1.1.3) is formatted to LF line ends;
/// a line break inside a string literal is its value and stays.
#[test]
fn fmt_writes_lf_and_keeps_literal_crlf() {
    let dir = scratch("fmt-crlf");
    let crlf = "fn f() {\r\n    let s = \"a\r\nb\";\r\n}\r\n";
    fs::write(dir.join("w.rok"), crlf).unwrap();
    assert_exit(&rokc(None, &dir, &["fmt", "--check", "w.rok"]), 1);
    assert_exit(&rokc(None, &dir, &["fmt", "w.rok"]), 0);
    assert_eq!(
        fs::read_to_string(dir.join("w.rok")).unwrap(),
        "fn f() {\n    let s = \"a\r\nb\";\n}\n"
    );
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
    // One path (`test`: and a filter); the REPL reads cells from stdin.
    assert_exit(&rokc(None, &dir, &["build", "a", "b"]), 2);
    assert_exit(&rokc(None, &dir, &["test", "a", "b", "c"]), 2);
    assert_exit(&rokc(None, &dir, &["repl", "-"]), 2);
    assert_exit(&rokc(None, &dir, &["--version"]), 0);
    let out = rokc(None, &dir, &["-V", "-v"]);
    assert!(
        text(&out.stdout).contains("\nhost: "),
        "{}",
        text(&out.stdout)
    );
    // Per-command help: the entry and its options only.
    let out = rokc(None, &dir, &["test", "--help"]);
    assert_exit(&out, 0);
    let help = text(&out.stdout);
    assert!(help.contains("test [path] [filter]") && help.contains("--threads=N"));
    assert!(
        !help.contains("demangle") && !help.contains("--iters"),
        "{help}"
    );
}

/// rokc's library and runtime are under its own sysroot (`bin/..`),
/// whatever `ROK_HOME` says; a missing one is named.
#[test]
fn sysroot_is_beside_rokc() {
    let dir = scratch("sysroot");
    let sys = dir.join("sys");
    fs::create_dir_all(sys.join("bin")).unwrap();
    fs::create_dir_all(sys.join("lib/rok/core")).unwrap();
    let rokc_exe = sys
        .join("bin")
        .join(format!("rokc{}", std::env::consts::EXE_SUFFIX));
    fs::copy(ROKC, &rokc_exe).unwrap();
    fs::write(sys.join("lib/rok/core/lib.rok"), "fn (\n").unwrap();
    fs::write(dir.join("x.rok"), "let x = 1;\n").unwrap();
    let run = |args: &[&str]| {
        Command::new(&rokc_exe)
            .current_dir(&dir)
            .env("ROK_HOME", workspace())
            .args(args)
            .output()
            .unwrap()
    };
    // Paths as `/`-separated, whatever the platform's separator.
    let stderr = |o: &std::process::Output| text(&o.stderr).replace('\\', "/");
    let out = run(&["check", "x.rok"]);
    assert_exit(&out, 1);
    assert!(stderr(&out).contains("sys/lib/rok/core/lib.rok"));
    fs::write(sys.join("lib/rok/core/lib.rok"), "").unwrap();
    let out = run(&["run", "x.rok"]);
    assert_exit(&out, 1);
    let err = stderr(&out);
    let rt = format!("sys/lib/{}", rokc_core::HOST_RUNTIME_LIB);
    assert!(
        err.contains("the runtime library is missing: no ") && err.contains(&rt),
        "{err}"
    );
}

/// `--target` links what the sysroot ships for it
/// (`lib/rok/targets/<triple>/`, `targets/build.sh`): Linux ELF
/// executables (musl static, glibc PIE through the system's loader; the
/// 32-bit ones ELFCLASS32), a 32-bit Windows PE (run with
/// `ROK_TEST_WINE=<wine>`, which needs its 32-bit support) and Mach-O
/// for the other macOS arch, run here under Rosetta. A target it does
/// not ship is named.
#[test]
fn cross_targets_link_from_the_sysroot() {
    let dir = scratch("cross");
    fs::write(
        dir.join("h.rok"),
        "fn main() -> i32 {\n    println(\"ok\");\n    0\n}\n",
    )
    .unwrap();
    let out = rokc(
        None,
        &dir,
        &["build", "h.rok", "--target", "riscv64gc-unknown-linux-gnu"],
    );
    assert_exit(&out, 1);
    let err = text(&out.stderr);
    assert!(
        err.contains("no runtime for riscv64gc-unknown-linux-gnu"),
        "{err}"
    );

    if setup().is_none() {
        return;
    }
    let targets = Path::new(ROKC).parent().unwrap().join("../lib/rok/targets");
    if !targets.is_dir() {
        eprintln!("skipped: no {} (targets/build.sh)", targets.display());
        return;
    }
    let rosetta = cfg!(all(target_os = "macos", target_arch = "aarch64"))
        && Command::new("arch")
            .args(["-x86_64", "/usr/bin/true"])
            .status()
            .is_ok_and(|s| s.success());
    let wine = std::env::var_os("ROK_TEST_WINE").filter(|w| !w.is_empty());
    for t in [
        "x86_64-unknown-linux-gnu",
        "aarch64-unknown-linux-gnu",
        "x86_64-unknown-linux-musl",
        "aarch64-unknown-linux-musl",
        "x86_64-apple-darwin",
        "i686-unknown-linux-gnu",
        "armv7-unknown-linux-gnueabihf",
        "i686-pc-windows-msvc",
    ] {
        if !targets.join(t).is_dir() {
            continue;
        }
        for o in ["-O0", "-O2"] {
            let exe = dir.join(format!("h-{t}{o}"));
            let exe_s = exe.display().to_string();
            let out = rokc(
                None,
                &dir,
                &["-q", "build", "h.rok", "--target", t, o, "-o", &exe_s],
            );
            assert_exit(&out, 0);
            let b = fs::read(&exe).unwrap();
            if t.contains("-linux") {
                check_linux_elf(t, &b);
            } else if t.contains("-windows") {
                check_x86_pe(t, &b);
                if let Some(wine) = &wine {
                    let run = Command::new(wine)
                        .arg(&exe)
                        .env("WINEDEBUG", "-all")
                        .output()
                        .unwrap();
                    assert_exit(&run, 0);
                    assert_eq!(text(&run.stdout).replace('\r', ""), "ok\n", "{t}");
                }
            } else {
                assert_eq!(&b[..4], &0xfeed_facf_u32.to_le_bytes(), "{t}");
                let cpu = u32::from_le_bytes([b[4], b[5], b[6], b[7]]);
                assert_eq!(cpu, 0x0100_0007, "{t}");
                if rosetta {
                    let run = Command::new("arch")
                        .arg("-x86_64")
                        .arg(&exe)
                        .output()
                        .unwrap();
                    assert_exit(&run, 0);
                    assert_eq!(text(&run.stdout), "ok\n");
                }
            }
        }
    }
}

/// A Linux executable for `t`: machine, class, static (musl) or a PIE
/// with glibc's loader and versions up to 2.34.
fn check_linux_elf(t: &str, b: &[u8]) {
    // (ELF machine, class, dynamic loader)
    let (machine, class, loader): (u16, u8, &[u8]) = match t.split('-').next().unwrap() {
        "x86_64" => (62, 2, b"/lib64/ld-linux-x86-64.so.2"),
        "aarch64" => (183, 2, b"/lib/ld-linux-aarch64.so.1"),
        "i686" => (3, 1, b"/lib/ld-linux.so.2"),
        _ => (40, 1, b"/lib/ld-linux-armhf.so.3"),
    };
    let has = |s: &[u8]| b.windows(s.len()).any(|w| w == s);
    assert_eq!(&b[..4], b"\x7fELF", "{t}");
    assert_eq!(b[4], class, "{t}: ELF class");
    assert_eq!(u16::from_le_bytes([b[18], b[19]]), machine, "{t}");
    let ty = u16::from_le_bytes([b[16], b[17]]);
    if t.ends_with("-musl") {
        assert_eq!(ty, 2, "{t}: a static ET_EXEC");
        assert!(!has(b"ld-linux"), "{t}");
    } else {
        assert_eq!(ty, 3, "{t}: a PIE");
        assert!(
            has(loader) && has(b"libc.so.6") && has(b"GLIBC_2.34"),
            "{t}"
        );
        assert!(!has(b"GLIBC_2.35"), "{t}: newer than glibc 2.34");
    }
}

/// An x86 PE image, large-address-aware.
fn check_x86_pe(t: &str, b: &[u8]) {
    assert_eq!(&b[..2], b"MZ", "{t}");
    let pe = u32::from_le_bytes(b[0x3c..0x40].try_into().unwrap()) as usize;
    assert_eq!(&b[pe..pe + 4], b"PE\0\0", "{t}");
    assert_eq!(u16::from_le_bytes([b[pe + 4], b[pe + 5]]), 0x14c, "{t}");
    // IMAGE_FILE_LARGE_ADDRESS_AWARE
    assert_ne!(b[pe + 22] & 0x20, 0, "{t}");
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
    // Prebuilt into deps/ with its fingerprint (902.3).
    for f in ["libgreet.a", "greet.rhir", "greet.fp"] {
        assert!(dir.join("app/target/debug/deps").join(f).is_file(), "{f}");
    }
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
/// Parameter and field defaults resolve in the package declaring them,
/// not in the caller's (spec 4.2.3): the app's own `one` / `LIMIT` / `S`
/// don't capture them.
#[test]
fn defaults_resolve_in_the_declaring_package() {
    let Some(env) = setup() else { return };
    let dir = scratch("extern-defaults");
    fs::create_dir_all(dir.join("dep")).unwrap();
    fs::write(
        dir.join("dep/lib.rok"),
        "fn one() -> i32 { 1 }\n\
         const LIMIT: i32 = 9;\n\
         pub struct S {\n    pub n: i32 = 5;\n}\n\
         pub struct Cfg {\n    pub f: fn() -> i32 = one;\n    pub k: i32 = LIMIT;\n}\n\
         pub fn use_s(s: S = S {}) -> i32 { s.n }\n\
         pub fn lim(x: i32 = LIMIT) -> i32 { x }\n\
         pub fn via_one<T>(t: T, x: i32 = one()) -> i32 { x }\n",
    )
    .unwrap();
    fs::create_dir_all(dir.join("app")).unwrap();
    fs::write(
        dir.join("app/main.rok"),
        "fn one() -> i32 { 100 }\nconst LIMIT: i32 = 200;\nstruct S {}\n\
         let c = dep::Cfg {};\n\
         println(f\"{(c.f)()} {c.k} {dep::use_s()} {dep::lim()} {dep::via_one(0)}\");\n",
    )
    .unwrap();
    let out = rokc(Some(&env), &dir, &["run", "app", "--extern", "dep=dep"]);
    assert_exit(&out, 0);
    assert_eq!(text(&out.stdout), "1 9 5 9 1\n");
}

/// A sum in a prebuilt dependency's signature has the same tags in the
/// app: member order does not follow the build's type numbering (the app
/// instantiates `Dict<str, i32>` before `List<i32>`, the library after).
#[test]
fn prebuilt_dependency_sums_keep_their_tags() {
    let Some(env) = setup() else { return };
    let dir = scratch("prebuilt-sums");
    fs::create_dir_all(dir.join("dep")).unwrap();
    fs::write(
        dir.join("dep/lib.rok"),
        "pub struct Zebra { pub n: i32; }\n\
         pub fn pick(b: bool) -> List<i32> | Dict<str, i32> {\n\
             if b { let xs: List<i32> = [1, 2, 3]; return xs; }\n\
             let d: Dict<str, i32> = Dict::new();\n\
             d[\"k\"] = 7;\n\
             return d;\n\
         }\n\
         pub fn size(x: List<i32> | Dict<str, i32> | Zebra) -> str {\n\
             match x {\n\
                 xs: List<i32> => f\"list {xs.len()}\",\n\
                 d: Dict<str, i32> => f\"dict {d.len()}\",\n\
                 z: Zebra => f\"zebra {z.n}\",\n\
             }\n\
         }\n",
    )
    .unwrap();
    fs::create_dir_all(dir.join("app")).unwrap();
    fs::write(
        dir.join("app/main.rok"),
        "struct Mine { a: i32; }\n\
         let early: Dict<str, i32> = Dict::new();\n\
         let m = Mine { a: early.len() as i32 };\n\
         println(dep::size(dep::pick(true)));\n\
         println(dep::size(dep::pick(false)));\n\
         println(dep::size(dep::Zebra { n: 4 + m.a }));\n\
         let own: Dict<str, i32> = Dict::new();\n\
         println(dep::size(own));\n",
    )
    .unwrap();
    let out = rokc(Some(&env), &dir, &["build", "dep"]);
    assert_exit(&out, 0);
    let rhir = dir.join("dep/target/debug/dep.rhir");
    let ext = format!("dep={}", rhir.display());
    let out = rokc(Some(&env), &dir, &["run", "-q", "app", "--extern", &ext]);
    assert_exit(&out, 0);
    assert_eq!(text(&out.stdout), "list 3\ndict 1\nzebra 4\ndict 0\n");
}

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
         impl Display for Bad { fn fmt(self, ref f: Formatter) throws (FmtError) { try f.write_str(f\"bad {self.at}\"); } }\n\
         impl Debug for Bad { fn fmt(self, ref f: Formatter) throws (FmtError) { try Display::fmt(self, ref f); } }\n\
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
/// `--check-library` lowers (so type-checks) every one of them.
#[test]
fn check_library_checks_every_body() {
    let dir = scratch("check-lib");
    fs::write(dir.join("main.rok"), "fn main() {}\n").unwrap();
    assert_exit(
        &rokc(None, &dir, &["check", "--check-library", "main.rok"]),
        0,
    );
}

#[test]
fn emit_expanded_prints_meta_expansions() {
    // Spec 6.9.9: `--emit=expanded` writes what user derives /
    // attributes generate, as source (the nested expansion of `Tag`'s
    // derive, used in the template at 11:5, is listed after the
    // attribute's).
    let dir = scratch("expanded");
    let src = "trait Named { fn type_name() -> str; }\n\
               #[impl_derive(Named)]\n\
               pub @derive {\n    impl Named for @Self {\n        \
               fn type_name() -> str { return @Self.as_str(); }\n    }\n}\n\
               #[impl_attribute(with_tag)]\n\
               pub @attribute {\n    @item\n    #[derive(Named)]\n    struct Tag {}\n}\n\
               #[with_tag]\nfn f() -> i32 { 1 }\n\
               println(Tag::type_name());\n";
    fs::write(dir.join("m.rok"), src).unwrap();
    let out = rokc(
        None,
        &dir,
        &["build", "m.rok", "--emit=expanded", "-o", "m.expanded.rok"],
    );
    assert_exit(&out, 0);
    let got = fs::read_to_string(dir.join("m.expanded.rok")).unwrap();
    let want = "// expanded from this `#[with_tag]` (m.rok:14:1)\n\
                fn f() -> i32 {\n    1\n}\n\
                #[derive(Named)]\nstruct Tag {\n}\n\n\
                // expanded from this `#[derive(Named)]` (m.rok:11:5)\n\
                impl Named for Tag {\n    fn type_name() -> str {\n        \
                return \"Tag\";\n    }\n}\n";
    assert_eq!(got, want);
}

#[test]
fn overflow_checks_option_overrides_the_opt_level() {
    let Some(env) = setup() else { return };
    let dir = scratch("ovf");
    fs::write(
        dir.join("ovf.rok"),
        "fn add(a: i32, b: i32) -> i32 { return a + b; }\nprintln(f\"{add(2147483647, 1)}\");\n",
    )
    .unwrap();
    let run = |args: &[&str]| rokc(Some(&env), &dir, &[&["run", "ovf.rok"], args].concat());
    assert_exit(&run(&["-O2", "-C", "overflow-checks"]), 101);
    assert_exit(&run(&["-O0", "-C", "overflow-checks=no"]), 0);
    assert_exit(&run(&["-C", "bogus"]), 2);
}

#[test]
fn dependency_trait_is_not_the_current_package() {
    let Some(env) = setup() else { return };
    let dir = scratch("clash");
    // Spec 4.9.6: a dependency's trait ranks with core's unless `use`d.
    fs::create_dir_all(dir.join("dz")).unwrap();
    fs::write(
        dir.join("dz/lib.rok"),
        "pub trait DepZero { fn zero() -> Self; }\n\
         impl DepZero for i32 { fn zero() -> i32 { return 7; } }\n",
    )
    .unwrap();
    fs::create_dir_all(dir.join("app")).unwrap();
    fs::write(dir.join("app/main.rok"), "println(f\"{i32::zero()}\");\n").unwrap();
    let out = rokc(Some(&env), &dir, &["run", "app", "--extern", "dz=dz"]);
    assert_exit(&out, 1);
    assert!(
        text(&out.stderr).contains("is ambiguous"),
        "{}",
        text(&out.stderr)
    );
    fs::write(
        dir.join("app/main.rok"),
        "use dz::DepZero;\nprintln(f\"{i32::zero()}\");\n",
    )
    .unwrap();
    let out = rokc(Some(&env), &dir, &["run", "app", "--extern", "dz=dz"]);
    assert_exit(&out, 0);
    assert_eq!(text(&out.stdout), "7\n");
}

/// Spec 2.9.5: a user impl overlapping a dependency's bounded blanket
/// impl is an error at its declaration; without the bound's impl for
/// the user type, the two are disjoint.
#[test]
fn dependency_blanket_impl_overlaps_user_impl() {
    let Some(env) = setup() else { return };
    let dir = scratch("overlap_dep");
    fs::create_dir_all(dir.join("dd")).unwrap();
    fs::write(
        dir.join("dd/lib.rok"),
        "pub trait Shape {}\n\
         pub trait Describe { fn d(self) -> i32; }\n\
         impl<T: Shape> Describe for T { fn d(self) -> i32 { return 1; } }\n",
    )
    .unwrap();
    fs::create_dir_all(dir.join("app")).unwrap();
    let main = "use dd::{Shape, Describe};\n\
                struct Mine<T> { v: T; }\n\
                impl<T> Describe for Mine<T> { fn d(self) -> i32 { return 2; } }\n\
                println(f\"{Mine { v: 1 }.d()}\");\n";
    fs::write(dir.join("app/main.rok"), main).unwrap();
    let out = rokc(Some(&env), &dir, &["run", "app", "--extern", "dd=dd"]);
    assert_exit(&out, 0);
    assert_eq!(text(&out.stdout), "2\n");
    fs::write(
        dir.join("app/main.rok"),
        format!("{main}impl<T> Shape for Mine<T> {{}}\n"),
    )
    .unwrap();
    let out = rokc(Some(&env), &dir, &["check", "app", "--extern", "dd=dd"]);
    assert_exit(&out, 1);
    assert!(
        text(&out.stderr).contains("overlap on `Mine<T>` — bounds don't make impls disjoint"),
        "{}",
        text(&out.stderr)
    );
}

#[test]
fn missing_mlir_plugins_are_errors() {
    // Stdlib bare 1.10.3: a missing plugin is a clean error up front.
    let dir = scratch("mlir-plugin");
    fs::write(dir.join("p.rok"), "println(\"hi\");\n").unwrap();
    let out = rokc(
        None,
        &dir,
        &["build", "p.rok", "--load-mlir-plugin", "/no/such/libd.so"],
    );
    assert_exit(&out, 1);
    assert!(
        text(&out.stderr).contains("no such file"),
        "{}",
        text(&out.stderr)
    );
    let out = rokc(
        None,
        &dir,
        &["build", "p.rok", "--load-mlir-plugin=nosuchdialect"],
    );
    assert_exit(&out, 1);
    assert!(
        text(&out.stderr).contains("ROK_MLIR_PLUGIN_PATH"),
        "{}",
        text(&out.stderr)
    );
    // A file that is no plugin is refused when loaded, which fails the
    // build.
    let Some(env) = setup() else { return };
    for flag in ["--load-mlir-plugin", "--load-mlir-pass-plugin"] {
        let out = rokc(Some(&env), &dir, &["build", "p.rok", flag, "p.rok"]);
        assert_exit(&out, 1);
        let err = text(&out.stderr);
        assert!(
            err.contains("LLVM back end failed") && err.contains("Failed to load"),
            "{err}"
        );
    }
}

/// A dialect + pass plugin (`tests/plugin/answer.cpp`) built from the
/// linked prefix's headers with its MLIR symbols unresolved runs on
/// rokc's own MLIR.
#[test]
fn mlir_plugin_binds_to_rokcs_mlir() {
    let Some(env) = setup() else { return };
    let prefix = rokc_llvm::PREFIX.expect("rokc links LLVM but names no prefix");
    let dir = scratch("mlir-plugin-run");
    let lib = dir.join(format!("librokt.{}", std::env::consts::DLL_EXTENSION));
    let mut cxx = Command::new("/usr/bin/c++");
    cxx.args([
        "-std=c++17",
        "-O1",
        "-fno-rtti",
        "-fno-exceptions",
        "-fPIC",
        "-fvisibility-inlines-hidden",
        "-w",
        "-shared",
    ])
    .arg(format!("-I{prefix}/include"))
    .arg(workspace().join("compiler/rokc/tests/plugin/answer.cpp"))
    .arg("-o")
    .arg(&lib);
    if cfg!(target_vendor = "apple") {
        cxx.args(["-mmacosx-version-min=11.0", "-undefined", "dynamic_lookup"]);
    }
    let out = cxx.output().unwrap();
    assert_exit(&out, 0);

    fs::write(
        dir.join("p.rok"),
        "use rok::bare::mlir::__mlir_op;\n\nfn main() -> i32 {\n    \
         let x: i32 = unsafe { __mlir_op::<\"rokt.answer\", i32>() };\n    \
         println(f\"{x}\");\n    0\n}\n",
    )
    .unwrap();
    let lib = lib.to_str().unwrap();
    let out = rokc(
        Some(&env),
        &dir,
        &[
            "build",
            "p.rok",
            "--load-mlir-plugin",
            lib,
            "--load-mlir-pass-plugin",
            lib,
            "--mlir-pass",
            "rokt-lower",
            "-o",
            "p",
        ],
    );
    assert_exit(&out, 0);
    let run = Command::new(dir.join("p")).output().unwrap();
    assert_eq!(text(&run.stdout), "42\n");
}

/// `rokc --print cfg` (spec 6.3.11): the target's keys and `--cfg`.
#[test]
fn print_cfg_lists_the_active_cfg() {
    let dir = scratch("print_cfg");
    let out = rokc(
        None,
        &dir,
        &[
            "--print",
            "cfg",
            "--target=x86_64-unknown-linux-gnu",
            "--cfg",
            "feature=gpu",
            "-O2",
        ],
    );
    assert_exit(&out, 0);
    assert_eq!(
        text(&out.stdout),
        "feature=\"gpu\"\ntarget_arch=\"x86_64\"\ntarget_endian=\"little\"\n\
         target_env=\"gnu\"\ntarget_family=\"unix\"\ntarget_os=\"linux\"\n\
         target_pointer_width=\"64\"\n"
    );
    let out = rokc(None, &dir, &["--print", "cfg"]);
    assert!(text(&out.stdout).starts_with("debug_assertions\n"));
    assert_exit(&rokc(None, &dir, &["--print", "sysroot"]), 2);
}

/// `isize` / `usize` limits follow the target's pointer width (stdlib
/// 2.1.4): a 32-bit target folds them to 32-bit values.
#[test]
fn pointer_sized_limits_follow_the_target() {
    let Some(env) = setup() else { return };
    let dir = scratch("pointer_width_limits");
    fs::write(
        dir.join("w.rok"),
        "#[export_name(\"t_max\")]\npub fn t_max() -> i64 { usize::MAX as i64 + \
         usize::BITS as i64 + isize::MIN as i64 }\nfn main() {}\n",
    )
    .unwrap();
    for (target, want) in [
        ("--target=i686-unknown-linux-gnu", "ret i64 2147483679"),
        (
            "--target=x86_64-unknown-linux-gnu",
            "ret i64 -9223372036854775745",
        ),
    ] {
        let out = rokc(
            Some(&env),
            &dir,
            &[
                "build",
                "-O2",
                "--emit=llvmir",
                target,
                "w.rok",
                "-o",
                "w.ll",
            ],
        );
        assert_exit(&out, 0);
        let ir = fs::read_to_string(dir.join("w.ll")).unwrap();
        assert!(ir.contains(want), "{target}: {ir}");
    }
}

/// `#[cfg]` on an impl member (stdlib 3.7.2 `Child::pidfd`, Linux only):
/// the method exists for a Linux target and not for macOS.
#[test]
fn cfg_on_impl_members_follows_the_target() {
    let dir = scratch("cfg_impl_member");
    fs::write(
        dir.join("p.rok"),
        "use rok::std::process::Command;\nfn main() {\n    \
         let c = try Command::new(\"true\").spawn() catch _ { return; };\n    \
         let fd = try c.pidfd() catch _ { -1 };\n    println(f\"{fd}\");\n}\n",
    )
    .unwrap();
    let check = |target: &str| rokc(None, &dir, &["check", target, "p.rok"]);
    assert_exit(&check("--target=x86_64-unknown-linux-gnu"), 0);
    let out = check("--target=aarch64-apple-darwin");
    assert_exit(&out, 1);
    assert!(text(&out.stderr).contains("no method `pidfd`"));
}

/// `#[non_exhaustive]` (spec 6.2.10): a match on the type from another
/// package needs a `_` arm even when it names every variant; inside its
/// own package it does not.
#[test]
fn non_exhaustive_needs_a_catch_all_across_packages() {
    let dir = scratch("non-exhaustive");
    fs::create_dir_all(dir.join("dep")).unwrap();
    fs::write(
        dir.join("dep/lib.rok"),
        "#[non_exhaustive]\npub enum E { A, B }\n\
         pub fn n(e: E) -> i32 { return match e { E::A => 1, E::B => 2 }; }\n",
    )
    .unwrap();
    fs::create_dir_all(dir.join("app")).unwrap();
    let main = |arms: &str| {
        fs::write(
            dir.join("app/main.rok"),
            format!("use dep::E;\nlet v = match E::A {{ {arms} }};\nprintln(f\"{{v}}\");\n"),
        )
        .unwrap();
    };
    main("E::A => 1, E::B => 2");
    let out = rokc(None, &dir, &["check", "app", "--extern", "dep=dep"]);
    assert_exit(&out, 1);
    assert!(
        text(&out.stderr).contains("needs a `_` arm"),
        "{}",
        text(&out.stderr)
    );
    main("E::A => 1, E::B => 2, _ => 3");
    assert_exit(
        &rokc(None, &dir, &["check", "app", "--extern", "dep=dep"]),
        0,
    );
}
