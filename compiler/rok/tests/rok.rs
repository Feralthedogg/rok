//! `rok` end to end: scratch `ROK_HOME`s, local git repositories made
//! with the `git` CLI, and the `rokc` built next to `rok`. Tests that
//! compile and run native code skip without the LLVM toolchain (unless
//! `ROK_REQUIRE_LLVM=1`).

// `HEAD^{tree}` is git revision syntax, not a format argument.
#![allow(clippy::literal_string_with_formatting_args)]

use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::sync::OnceLock;

const ROK: &str = env!("CARGO_BIN_EXE_rok");

fn workspace() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// `rok` runs the `rokc` beside it (and tests that link want the
/// runtime): build both once.
fn build_rokc() {
    static BUILT: OnceLock<bool> = OnceLock::new();
    let ok = *BUILT.get_or_init(|| {
        let cargo = std::env::var("CARGO").unwrap_or_else(|_| "cargo".into());
        Command::new(cargo)
            .args(["build", "-p", "rokc", "-p", "rokr"])
            .current_dir(workspace())
            .status()
            .unwrap()
            .success()
    });
    assert!(ok, "cargo build -p rokc -p rokr failed");
}

fn llvm() -> bool {
    let path = std::env::var_os("PATH").unwrap_or_default();
    let found = ["mlir-opt", "mlir-translate", "clang"]
        .iter()
        .all(|t| std::env::split_paths(&path).any(|d| d.join(t).is_file()));
    if !found {
        assert!(
            std::env::var("ROK_REQUIRE_LLVM").as_deref() != Ok("1"),
            "ROK_REQUIRE_LLVM=1 but the LLVM tools are not on PATH"
        );
    }
    found
}

fn scratch(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rok-test-{}-{name}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    fs::canonicalize(dir).unwrap()
}

fn write(path: &Path, text: &str) {
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, text).unwrap();
}

fn read(path: &Path) -> String {
    fs::read_to_string(path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
}

fn text(b: &[u8]) -> String {
    String::from_utf8_lossy(b).into_owned()
}

fn rok_cmd(home: &Path, cwd: &Path, args: &[&str]) -> Command {
    build_rokc();
    let mut c = Command::new(ROK);
    c.current_dir(cwd)
        .env("ROK_HOME", home)
        .env_remove("ROK_ENV")
        .env_remove("ROK_REGISTRY")
        .args(args);
    c
}

fn rok(home: &Path, cwd: &Path, args: &[&str]) -> Output {
    rok_cmd(home, cwd, args).output().unwrap()
}

#[track_caller]
fn ok(out: &Output) -> String {
    assert_eq!(
        out.status.code(),
        Some(0),
        "stdout: {}\nstderr: {}",
        text(&out.stdout),
        text(&out.stderr)
    );
    text(&out.stdout)
}

#[track_caller]
fn fails(out: &Output, want: &str) {
    let err = text(&out.stderr);
    assert_ne!(out.status.code(), Some(0), "unexpected success: {err}");
    assert!(err.contains(want), "stderr lacks {want:?}:\n{err}");
}

fn git(dir: &Path, args: &[&str]) -> String {
    let out = Command::new("git")
        .current_dir(dir)
        .args([
            "-c",
            "user.name=t",
            "-c",
            "user.email=t@t",
            "-c",
            "commit.gpgsign=false",
        ])
        .args(args)
        .env_remove("GIT_DIR")
        .output()
        .unwrap();
    assert!(out.status.success(), "git {args:?}: {}", text(&out.stderr));
    text(&out.stdout).trim().to_owned()
}

/// A git repository at `dir` holding `files`; the new commit.
fn commit(dir: &Path, files: &[(&str, &str)]) -> String {
    if !dir.join(".git").exists() {
        fs::create_dir_all(dir).unwrap();
        git(dir, &["init", "-q", "-b", "main"]);
    }
    for (name, body) in files {
        write(&dir.join(name), body);
    }
    git(dir, &["add", "-A"]);
    git(dir, &["commit", "-q", "-m", "c"]);
    git(dir, &["rev-parse", "HEAD"])
}

/// `name=path` lines of `rok deps`.
fn deps(home: &Path, cwd: &Path, extra: &[&str]) -> Vec<(String, String)> {
    let mut args = extra.to_vec();
    args.push("deps");
    ok(&rok(home, cwd, &args))
        .lines()
        .map(|l| {
            let (n, p) = l.split_once('=').unwrap();
            (n.to_owned(), p.to_owned())
        })
        .collect()
}

const LIB_V1: &str = "pub fn greet() -> i32 { return 1; }\n";
const LIB_V2: &str = "pub fn greet() -> i32 { return 2; }\n";

/// A manifest with comments, which `add` / `remove` keep.
const APP0: &str = "// my app\nPackage {\n    name: \"app\", // keep\n    deps: {\n        // deps go here\n    },\n}\n";

#[test]
fn add_lock_update_offline_remove() {
    let root = scratch("lock");
    let home = root.join("home");
    let repo = root.join("greet");
    let c1 = commit(&repo, &[("lib.rok", LIB_V1)]);
    let url = repo.display().to_string();
    let app = root.join("app");
    write(
        &app.join("main.rok"),
        "use greet::greet;\nprintln(f\"{greet()}\");\n",
    );
    write(&app.join("rok.rokon"), APP0);

    ok(&rok(&home, &app, &["add", "greet", "--git", &url]));
    let manifest = read(&app.join("rok.rokon"));
    assert_eq!(
        manifest,
        APP0.replace(
            "    },",
            &format!("        \"greet\": Dep::git(\"{url}\"),\n    }},")
        )
    );
    let lock = read(&app.join("rok.lock"));
    let tree = git(&repo, &["rev-parse", "HEAD^{tree}"]);
    assert!(
        lock.starts_with(
            "// rok.lock: generated by `rok`; do not edit. Commit it with your sources.\n\
             Lock {\n    version: 1,\n    packages: [\n        Locked {\n            \
             name: \"greet\",\n"
        ),
        "{lock}"
    );
    for want in [
        format!("\"{url}\""),
        format!("commit: \"{c1}\",\n            tree: \"{tree}\",\n        }},\n    ],\n}}\n"),
    ] {
        assert!(lock.contains(&want), "{lock}");
    }
    let checkout = home.join("cache/git/checkouts").join(&c1);
    assert_eq!(
        deps(&home, &app, &[]),
        [(
            "greet".to_owned(),
            checkout.join("lib.rok").display().to_string()
        )]
    );

    // A new commit upstream: builds keep the locked one; `update` moves.
    let c2 = commit(&repo, &[("lib.rok", LIB_V2)]);
    assert!(deps(&home, &app, &["--locked"])[0].1.contains(&c1));
    ok(&rok(&home, &app, &["update", "greet"]));
    assert!(read(&app.join("rok.lock")).contains(&c2));
    assert!(deps(&home, &app, &[])[0].1.contains(&c2));
    fails(&rok(&home, &app, &["update", "nope"]), "not a dependency");

    // Offline: a modified or missing checkout comes back from the cached
    // clone; nothing is fetched.
    let c2_dir = home.join("cache/git/checkouts").join(&c2);
    write(&c2_dir.join("lib.rok"), "tampered");
    let out = rok(&home, &app, &["--offline", "deps"]);
    ok(&out);
    assert!(
        text(&out.stderr).contains("was modified"),
        "{}",
        text(&out.stderr)
    );
    assert_eq!(read(&c2_dir.join("lib.rok")), LIB_V2);
    fs::remove_dir_all(&c2_dir).unwrap();
    ok(&rok(&home, &app, &["--offline", "deps"]));
    // `update --offline` re-resolves against the cached clone.
    ok(&rok(&home, &app, &["--offline", "update"]));
    // A fresh ROK_HOME has no cache: offline fails, online fetches the
    // locked commit.
    let home2 = root.join("home2");
    fails(&rok(&home2, &app, &["--offline", "deps"]), "--offline");
    assert!(deps(&home2, &app, &[])[0].1.contains(&c2));

    // --locked refuses to change the lock.
    let other = "\n        \"other\": Dep::git(\"/nope\"),";
    write(
        &app.join("rok.rokon"),
        &read(&app.join("rok.rokon")).replace("deps: {", &format!("deps: {{{other}")),
    );
    fails(&rok(&home, &app, &["--locked", "deps"]), "--locked");
    write(
        &app.join("rok.rokon"),
        &read(&app.join("rok.rokon")).replace(other, ""),
    );

    // A tag; `remove` edits the file and prunes the lock.
    git(&repo, &["tag", "v1", &c1]);
    ok(&rok(
        &home,
        &app,
        &["add", "greet", "--git", &url, "--tag", "v1"],
    ));
    assert!(
        read(&app.join("rok.rokon"))
            .contains(&format!("\"greet\": Dep::git(\"{url}\", tag: \"v1\"),"))
    );
    assert!(read(&app.join("rok.lock")).contains("tag: \"v1\""));
    assert!(read(&app.join("rok.lock")).contains(&format!("commit: \"{c1}\"")));
    ok(&rok(&home, &app, &["remove", "greet"]));
    assert_eq!(read(&app.join("rok.rokon")), APP0);
    assert!(!read(&app.join("rok.lock")).contains("Locked"));
    fails(&rok(&home, &app, &["remove", "greet"]), "not a dependency");

    // A bad source leaves rok.rokon as it was.
    let before = read(&app.join("rok.rokon"));
    fails(
        &rok(
            &home,
            &app,
            &[
                "add",
                "x",
                "--git",
                &root.join("missing").display().to_string(),
            ],
        ),
        "cannot fetch",
    );
    assert_eq!(read(&app.join("rok.rokon")), before);
    fails(
        &rok(&home, &app, &["add", "My.X", "--path", "."]),
        "try `my-x`",
    );
}

#[test]
fn transitive_dependencies_and_conflicts() {
    let root = scratch("transitive");
    let home = root.join("home");
    let b = root.join("b");
    commit(&b, &[("lib.rok", "pub fn b() -> i32 { return 2; }\n")]);
    let a = root.join("a");
    commit(
        &a,
        &[
            ("lib.rok", "pub fn a() -> i32 { return 1; }\n"),
            (
                "rok.rokon",
                &format!(
                    "Package {{ name: \"a\", deps: {{ \"b\": Dep::git(\"{}\") }} }}\n",
                    b.display()
                ),
            ),
        ],
    );
    let app = root.join("app");
    write(&app.join("main.rok"), "println(\"x\");\n");
    ok(&rok(
        &home,
        &app,
        &["add", "a", "--git", &a.display().to_string()],
    ));
    let names: Vec<String> = deps(&home, &app, &[]).into_iter().map(|(n, _)| n).collect();
    // Each package after its own dependencies.
    assert_eq!(names, ["b", "a"]);
    let lock = read(&app.join("rok.lock"));
    assert!(
        lock.contains("name: \"a\"") && lock.contains("name: \"b\""),
        "{lock}"
    );

    // `b` from a path as well: two packages named `b`.
    let other_b = root.join("other_b");
    write(
        &other_b.join("lib.rok"),
        "pub fn b() -> i32 { return 3; }\n",
    );
    let before = read(&app.join("rok.rokon"));
    fails(
        &rok(&home, &app, &["add", "b", "--path", "../other_b"]),
        "conflicting requirements for package `b`",
    );
    assert_eq!(read(&app.join("rok.rokon")), before);

    // Path dependencies are written relative to the project; a
    // non-library is refused.
    write(&root.join("tool/main.rok"), "println(\"t\");\n");
    fails(
        &rok(&home, &app, &["add", "tool", "--path", "../tool"]),
        "not a library package",
    );
    ok(&rok(
        &home,
        &app,
        &["add", "c", "--path", "../other_b", "--dev"],
    ));
    assert!(
        read(&app.join("rok.rokon"))
            .contains("    dev_deps: {\n        \"c\": Dep::path(\"../other_b\"),\n    },\n}\n")
    );
    // Dev dependencies are for tests only.
    assert_eq!(deps(&home, &app, &[]).len(), 2);
    assert_eq!(ok(&rok(&home, &app, &["deps", "--dev"])).lines().count(), 3);
}

#[test]
fn manifest_errors_and_reserved_forms() {
    let root = scratch("manifest");
    let home = root.join("home");
    let app = root.join("app");
    write(&app.join("main.rok"), "println(\"x\");\n");
    write(
        &app.join("rok.rokon"),
        "Package {\n    deps: { \"foo\": \"1.0.x.y\" },\n}\n",
    );
    let out = rok(&home, &app, &["deps"]);
    fails(&out, "is not a version requirement");
    assert!(
        text(&out.stderr).contains("rok.rokon:2:20"),
        "{}",
        text(&out.stderr)
    );
    write(
        &app.join("rok.rokon"),
        "Package { deps: { \"foo\": Dep::native(\"z\") } }\n",
    );
    fails(
        &rok(&home, &app, &["deps"]),
        "reserved and not supported yet",
    );
    write(
        &app.join("rok.rokon"),
        "Package {\n    name: env(\"X\"),\n}\n",
    );
    let out = rok(&home, &app, &["deps"]);
    fails(&out, "error[E002]: calls are not allowed in RokON");
    fails(&out, "rok.rokon:2:11\n");
    write(&app.join("rok.rokon"), "Package { deps: {\n");
    fails(&rok(&home, &app, &["deps"]), "rok.rokon:2:1\n");
    write(&app.join("rok.rokon"), "Package {}\n");
    ok(&rok(&home, &app, &["deps"]));
    fs::remove_file(app.join("rok.rokon")).unwrap();

    // A wrongly cased manifest is ignored with a warning.
    write(&app.join("Rok.rokon"), "Package { deps: { \"x\": 1 } }\n");
    let out = rok(&home, &app, &["deps"]);
    ok(&out);
    assert!(
        text(&out.stderr).contains("the manifest is named `rok.rokon` (lowercase)"),
        "{}",
        text(&out.stderr)
    );
}

#[test]
fn new_and_init_write_a_manifest() {
    let root = scratch("new");
    let home = root.join("home");
    ok(&rok(&home, &root, &["new", "--lib", "mylib"]));
    assert!(root.join("mylib/lib.rok").is_file());
    assert_eq!(
        read(&root.join("mylib/rok.rokon")),
        "Package { name: \"mylib\", version: \"0.1.0\", deps: {} }\n"
    );
    // Its own git repository, ignoring target/.
    assert_eq!(read(&root.join("mylib/.gitignore")), "target/\n");
    assert!(root.join("mylib/.git").is_dir());
    // Package names: `[a-z][a-z0-9_-]*`.
    fails(&rok(&home, &root, &["new", "My App"]), "try `my-app`");
    assert!(!root.join("My App").exists());
    let dir = root.join("Existing.Dir");
    fs::create_dir_all(&dir).unwrap();
    // Inside a repository: no new one.
    git(&dir, &["init", "-q"]);
    let out = rok(&home, &dir, &["init"]);
    ok(&out);
    assert!(text(&out.stderr).contains("the package name is `existing-dir`"));
    assert!(dir.join("main.rok").is_file());
    assert!(read(&dir.join("rok.rokon")).contains("name: \"existing-dir\""));
    fs::create_dir_all(dir.join("sub")).unwrap();
    ok(&rok(&home, &dir.join("sub"), &["new", "inner"]));
    assert!(!dir.join("sub/inner/.git").exists());
    fails(&rok(&home, &dir, &["init"]), "already exists");
    let version = ok(&rok(&home, &dir, &["--version"]));
    assert!(
        version.starts_with(&format!("rok {}", env!("CARGO_PKG_VERSION"))),
        "{version}"
    );
    // Usage errors exit 2 (spec 9.1.6); the rest 1.
    let usage = |args: &[&str]| rok(&home, &root, args).status.code();
    assert_eq!(usage(&["new"]), Some(2));
    assert_eq!(usage(&["add", "x", "--frob"]), Some(2));
    assert_eq!(usage(&["frob"]), Some(2));
    assert_eq!(usage(&["toolchain", "frob"]), Some(2));
    // A command on a package, outside one: rok says so.
    let out = rok(&home, &root, &["check"]);
    assert_eq!(out.status.code(), Some(1));
    assert!(
        text(&out.stderr).starts_with("rok: error: not inside a package"),
        "{}",
        text(&out.stderr)
    );
    // Per-command help.
    let help = ok(&rok(&home, &root, &["add", "--help"]));
    assert!(help.contains("add <name> --path <dir>") && !help.contains("publish"));
    assert_eq!(ok(&rok(&home, &root, &["help", "add"])), help);
    let help = ok(&rok(&home, &root, &["test", "--help"]));
    assert!(
        help.contains("--threads") && !help.contains("--iters"),
        "{help}"
    );
}

#[test]
fn rok_add_writes_canonical_rokon() {
    let root = scratch("canon");
    let home = root.join("home");
    write(&root.join("u/lib.rok"), LIB_V1);
    ok(&rok(&home, &root, &["new", "app"]));
    let app = root.join("app");
    ok(&rok(&home, &app, &["add", "u", "--path", "../u"]));
    // Fits in 100 columns: one line.
    assert_eq!(
        read(&app.join("rok.rokon")),
        "Package { name: \"app\", version: \"0.1.0\", deps: { \"u\": Dep::path(\"../u\") } }\n"
    );
    ok(&rok(
        &home,
        &app,
        &["add", "a_rather_long_dependency_name", "--path", "../u"],
    ));
    assert_eq!(
        read(&app.join("rok.rokon")),
        "Package {\n    name: \"app\",\n    version: \"0.1.0\",\n    deps: { \"u\": \
         Dep::path(\"../u\"), \"a_rather_long_dependency_name\": Dep::path(\"../u\") },\n}\n"
    );
    // A file with comments keeps its layout.
    let mine = "// mine\nPackage { name: \"app\", deps: { \"u\": Dep::path(\"../u\") } }\n";
    write(&app.join("rok.rokon"), mine);
    ok(&rok(&home, &app, &["remove", "u"]));
    assert!(read(&app.join("rok.rokon")).starts_with("// mine\nPackage { name: \"app\""));
    // The manifest's name is the package's.
    write(
        &app.join("rok.rokon"),
        "Package { name: \"hello\", deps: {} }\n",
    );
    let out = rok(&home, &app, &["build"]);
    if llvm() {
        ok(&out);
        assert!(app.join("target/debug/hello").is_file());
    }
    write(&app.join("rok.rokon"), "Package { name: \"My_App\" }\n");
    fails(&rok(&home, &app, &["check"]), "try `my_app`");

    // `my-lib` is a package name; code says `my_lib`. `-` and `_` are one
    // name, so both spellings cannot be dependencies.
    ok(&rok(&home, &root, &["new", "--lib", "my-lib"]));
    assert!(read(&root.join("my-lib/rok.rokon")).contains("name: \"my-lib\""));
    write(&app.join("rok.rokon"), "Package { name: \"my-app\" }\n");
    write(
        &app.join("main.rok"),
        "use my_lib::add;\nprintln(f\"{add(1, 2)}\");\n",
    );
    ok(&rok(&home, &app, &["add", "my-lib", "--path", "../my-lib"]));
    ok(&rok(&home, &app, &["-q", "check"]));
    assert!(ok(&rok(&home, &app, &["deps"])).starts_with("my_lib="));
    fails(
        &rok(&home, &app, &["add", "my_lib", "--path", "../my-lib"]),
        "are the same package",
    );
    if llvm() {
        assert_eq!(ok(&rok(&home, &app, &["-q", "run"])), "3\n");
        assert!(app.join("target/debug/my-app").is_file());
    }
}

#[test]
fn lint_and_doc_with_dependencies() {
    let root = scratch("lintdoc");
    let home = root.join("home");
    write(
        &root.join("util/lib.rok"),
        "/// Says hi.\npub fn hello() -> i32 { let unused = 1; 1 }\n",
    );
    let app = root.join("app");
    write(
        &app.join("rok.rokon"),
        "Package {\n    name: \"app\",\n    deps: { \"util\": Dep::path(\"../util\") },\n    \
         lints: { \"unused_variables\": \"deny\" },\n}\n",
    );
    write(
        &app.join("main.rok"),
        "use util::hello;\nlet x = hello();\nprintln(\"hi\");\n",
    );
    // `lints` sets the level, the command line overrides it, and the
    // dependency is not linted.
    let out = rok(&home, &app, &["lint"]);
    fails(&out, "unused variable `x`");
    assert!(
        !text(&out.stderr).contains("`unused`"),
        "{}",
        text(&out.stderr)
    );
    let out = rok(&home, &app, &["lint", "-W", "unused_variables"]);
    ok(&out);
    assert!(text(&out.stderr).contains("warning[E503]"));
    fails(
        &rok(&home, &app, &["lint", "-D", "all"]),
        "unused variable `x`",
    );

    ok(&rok(&home, &app, &["-q", "doc"]));
    assert!(read(&app.join("target/doc/util/index.html")).contains("Says hi."));
    assert!(read(&app.join("target/doc/index.html")).contains("app/index.html"));
}

#[test]
fn named_environments() {
    let root = scratch("envs");
    let home = root.join("home");
    let lib = root.join("lib1");
    write(&lib.join("lib.rok"), LIB_V1);
    let elsewhere = root.join("elsewhere");
    fs::create_dir_all(&elsewhere).unwrap();

    ok(&rok(&home, &root, &["env", "create", "work"]));
    // `rok --env work jupyter install`: a kernelspec that runs the
    // kernel in that environment.
    let jupyter = root.join("jupyter");
    ok(
        &rok_cmd(&home, &root, &["--env", "work", "jupyter", "install"])
            .env("JUPYTER_DATA_DIR", &jupyter)
            .output()
            .unwrap(),
    );
    let spec = read(&jupyter.join("kernels/rok-work/kernel.json"));
    assert!(
        spec.contains(r#""--env","work","jupyter","--connection-file","{connection_file}"],"display_name":"rok (work)""#),
        "{spec}"
    );
    // A kernel started from a GUI still finds the tools.
    assert!(spec.contains(r#""env":{"ROK_HOME":"#) && spec.contains(r#""PATH":"#));
    fails(
        &rok(&home, &root, &["env", "create", "work"]),
        "already exists",
    );
    ok(&rok(
        &home,
        &root,
        &["add", "--env", "work", "greet", "--path", "lib1"],
    ));
    // In an environment, path dependencies are absolute.
    assert!(
        read(&home.join("envs/work/rok.rokon"))
            .contains(&format!("\"greet\": Dep::path(\"{}\"),", lib.display()))
    );
    assert_eq!(deps(&home, &elsewhere, &["--env", "work"])[0].0, "greet");
    // Outside a project: `default` (empty), then what `env use` chose,
    // and $ROK_ENV over both.
    assert!(deps(&home, &elsewhere, &[]).is_empty());
    ok(&rok(&home, &root, &["env", "use", "work"]));
    assert_eq!(deps(&home, &elsewhere, &[])[0].0, "greet");
    ok(&rok(
        &home,
        &root,
        &["add", "--env", "default", "d", "--path", "lib1"],
    ));
    let out = rok_cmd(&home, &elsewhere, &["deps"])
        .env("ROK_ENV", "default")
        .output()
        .unwrap();
    assert_eq!(ok(&out).split('=').next(), Some("d"));
    let list = ok(&rok(&home, &root, &["env", "list"]));
    assert_eq!(list, "  default\n* work\n");

    // Export, import elsewhere.
    let export = root.join("export");
    ok(&rok(&home, &root, &["env", "export", "work", "export"]));
    assert!(export.join("rok.rokon").is_file());
    ok(&rok(&home, &root, &["env", "import", "copy", "export"]));
    assert_eq!(deps(&home, &elsewhere, &["--env", "copy"])[0].0, "greet");
    // Import from a project: relative paths become absolute.
    let proj = root.join("proj");
    write(&proj.join("main.rok"), "println(\"p\");\n");
    write(
        &proj.join("rok.rokon"),
        "Package {\n    deps: {\n        \"g\": Dep::path(\"../lib1\"), // here\n    },\n}\n",
    );
    ok(&rok(&home, &root, &["env", "import", "fromproj", "proj"]));
    assert!(
        read(&home.join("envs/fromproj/rok.rokon"))
            .contains(&format!("\"g\": Dep::path(\"{}\"), // here", lib.display()))
    );

    // `env shell`: $SHELL with ROK_ENV and rok on PATH.
    let mut child = rok_cmd(&home, &root, &["env", "shell", "work"])
        .env("SHELL", "/bin/sh")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(b"echo \"env=$ROK_ENV\"; command -v rok\n")
        .unwrap();
    let out = child.wait_with_output().unwrap();
    let stdout = ok(&out);
    assert!(stdout.contains("env=work"), "{stdout}");
    assert!(stdout.contains(ROK), "{stdout}");

    ok(&rok(&home, &root, &["env", "remove", "work"]));
    fails(
        &rok(&home, &root, &["env", "remove", "work"]),
        "no environment",
    );
    fails(
        &rok(&home, &elsewhere, &["--env", "work", "deps"]),
        "no environment `work`",
    );
    // The choice went with it: back to `default`.
    assert_eq!(deps(&home, &elsewhere, &[])[0].0, "d");
}

/// A fake toolchain `version` in `dir`: the real `rok`, and a `rokc`
/// that says which toolchain it is and how it was called.
#[cfg(unix)]
fn fake_toolchain(dir: &Path, version: &str) {
    use std::os::unix::fs::PermissionsExt;
    let host = env!("ROK_HOST");
    write(
        &dir.join("bin/rokc"),
        &format!(
            "#!/bin/sh\nif [ \"$1\" = --version ]; then echo 'rokc {version} (fake)'; echo \
             'host: {host}'; exit 0; fi\necho \"rokc {version}: $*\"\n"
        ),
    );
    fs::set_permissions(dir.join("bin/rokc"), fs::Permissions::from_mode(0o755)).unwrap();
    fs::copy(ROK, dir.join("bin/rok")).unwrap();
    write(&dir.join("bin/rokls"), "");
    write(&dir.join("lib/librokr.a"), "");
    write(&dir.join("lib/rok/core/lib.rok"), "");
}

#[cfg(unix)]
#[test]
fn pinned_toolchains() {
    let root = scratch("toolchain");
    let home = root.join("home");
    let app = root.join("app");
    let host = env!("ROK_HOST");
    write(&app.join("main.rok"), "println(\"x\");\n");
    write(&app.join("rok.rokon"), "Package { toolchain: \"9.9\" }\n");
    fails(&rok(&home, &app, &["build"]), "rok toolchain install 9.9");

    fake_toolchain(&root.join("fake1"), "9.9.1");
    fake_toolchain(&root.join("fake2/rok-9.10.0"), "9.10.0");
    let tc = |args: &[&str]| rok(&home, &root, &[&["toolchain"][..], args].concat());
    assert_eq!(tc(&["install", "9.9.1"]).status.code(), Some(2));
    fails(&tc(&["install", "9.9.1", "--from", "app"]), "no bin/rokc");
    // The version is the toolchain's own (`bin/rokc --version`).
    fails(
        &tc(&["install", "9.11", "--from", "fake1"]),
        "is rokc 9.9.1, not 9.11",
    );
    ok(&tc(&["install", "9.9.1", "--from", "fake1"]));
    // A tarball with one top directory.
    let tar = Command::new("tar")
        .current_dir(root.join("fake2"))
        .args(["-czf", "../tc.tar.gz", "rok-9.10.0"])
        .status()
        .unwrap();
    assert!(tar.success());
    ok(&tc(&["install", "9.10", "--from", "tc.tar.gz"]));
    assert!(
        home.join(format!("toolchains/9.10.0-{host}/bin/rokc"))
            .is_file()
    );
    // The first one became the default, with the proxies.
    assert_eq!(
        ok(&tc(&["list"])),
        format!("9.9.1-{host} (default)\n9.10.0-{host}\n")
    );
    assert!(home.join("bin/rok").is_file() && home.join("bin/rokc").is_file());

    // The proxies (no ROK_HOME: theirs is where they are). Precedence:
    // `+<version>` > ROK_TOOLCHAIN > rok.rokon > the default.
    let proxy = |tool: &str, cwd: &Path, env: Option<&str>, args: &[&str]| {
        let mut c = Command::new(home.join("bin").join(tool));
        c.current_dir(cwd).env_remove("ROK_HOME").args(args);
        match env {
            Some(t) => c.env("ROK_TOOLCHAIN", t),
            None => c.env_remove("ROK_TOOLCHAIN"),
        };
        ok(&c.output().unwrap())
    };
    assert_eq!(proxy("rokc", &root, None, &["x"]), "rokc 9.9.1: x\n");
    let out = rok(&home, &root, &["toolchain", "default", "9.10"]);
    ok(&out);
    assert_eq!(proxy("rokc", &root, None, &["x"]), "rokc 9.10.0: x\n");
    assert_eq!(proxy("rokc", &app, None, &["x"]), "rokc 9.9.1: x\n");
    assert_eq!(
        proxy("rokc", &app, Some("9.10"), &["x"]),
        "rokc 9.10.0: x\n"
    );
    assert_eq!(
        proxy("rokc", &app, Some("9.10"), &["+9.9", "x"]),
        "rokc 9.9.1: x\n"
    );
    // The proxy `rok` runs the toolchain's `rok`, which runs its pin's
    // `rokc` with the arguments for it.
    assert_eq!(
        proxy("rok", &app, None, &["-q", "build", "--release"]),
        "rokc 9.9.1: -q build --release\n"
    );
    assert_eq!(
        proxy("rok", &root, None, &["+9.9", "-q", "fmt"]),
        "rokc 9.9.1: -q fmt\n"
    );
    // `rok toolchain` through the proxy is the proxy's own.
    assert_eq!(
        proxy("rok", &root, None, &["toolchain", "default"]),
        "9.10\n"
    );
    // An unknown pin names where it came from.
    write(&app.join("rok.rokon"), "Package { toolchain: \"9.8\" }\n");
    let out = Command::new(home.join("bin/rokc"))
        .current_dir(&app)
        .env_remove("ROK_TOOLCHAIN")
        .output()
        .unwrap();
    fails(&out, "toolchain 9.8 (pinned by ");

    ok(&tc(&["remove", "9.9.1"]));
    fails(&tc(&["remove", "9.9.1"]), "is not installed");
    assert_eq!(ok(&tc(&["list"])), format!("9.10.0-{host} (default)\n"));
    // Pinning this rok's own version runs the rokc beside it.
    let mine: String = env!("CARGO_PKG_VERSION")
        .split('.')
        .take(2)
        .collect::<Vec<_>>()
        .join(".");
    write(
        &app.join("rok.rokon"),
        &format!("Package {{ toolchain: \"{mine}\" }}\n"),
    );
    ok(&rok(&home, &app, &["-q", "check"]));
}

#[test]
fn script_dependencies() {
    let root = scratch("script");
    let home = root.join("home");
    write(&root.join("lib1/lib.rok"), LIB_V1);
    let script = "//! ```rokon\n//! Package {\n//!     deps: { \"greet\": Dep::path(\"lib1\") },\n//! }\n//! ```\n\
                  use greet::greet;\nprintln(f\"{greet()}\");\n";
    write(&root.join("s.rok"), script);
    ok(&rok(&home, &root, &["-q", "check", "s.rok"]));
    // Its lock lives in the cache, not next to the script.
    assert!(!root.join("rok.lock").exists());
    assert!(home.join("cache/scripts").is_dir());
    write(
        &root.join("plain.rok"),
        "use greet::greet;\nprintln(f\"{greet()}\");\n",
    );
    assert_eq!(
        rok(&home, &root, &["-q", "check", "plain.rok"])
            .status
            .code(),
        Some(1)
    );
    write(
        &root.join("bad.rok"),
        "//! ```rokon\n//! Package {\n//!     deps: { \"g\": 1 },\n//! }\n//! ```\n",
    );
    fails(
        &rok(&home, &root, &["check", "bad.rok"]),
        "bad.rok (//! rokon block):2:18",
    );

    if llvm() {
        let out = rok(&home, &root, &["-q", "run", "s.rok"]);
        assert_eq!(ok(&out), "1\n");
    }
}

#[test]
fn build_run_and_repl_with_dependencies() {
    if !llvm() {
        return;
    }
    let root = scratch("e2e");
    let home = root.join("home");
    let repo = root.join("greet");
    commit(&repo, &[("lib.rok", LIB_V2)]);
    let app = root.join("app");
    ok(&rok(&home, &root, &["new", "app"]));
    write(
        &app.join("main.rok"),
        "use greet::greet;\nprintln(f\"{greet()}\");\n",
    );
    ok(&rok(
        &home,
        &app,
        &["add", "greet", "--git", &repo.display().to_string()],
    ));
    assert_eq!(ok(&rok(&home, &app, &["-q", "run"])), "2\n");
    assert!(app.join("target/debug/app").is_file());
    // `repl <path>`: the session has the program's imports and dependencies.
    let mut child = rok_cmd(&home, &root, &["-q", "repl", "app"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(b":type greet()\ngreet() + 1\n")
        .unwrap();
    let out = child.wait_with_output().unwrap();
    assert_eq!(ok(&out), "2\ni32\ni32: 3\n", "{}", text(&out.stderr));
    ok(&rok(&home, &app, &["-q", "build", "--release"]));
    assert!(app.join("target/release/app").is_file());
    ok(&rok(&home, &app, &["-q", "clean"]));
    assert!(!app.join("target").exists());

    // `:add` in the REPL goes to the active environment; bare `rok` is `rok repl`.
    write(&root.join("lib1/lib.rok"), LIB_V1);
    ok(&rok(&home, &root, &["env", "create", "r"]));
    let mut child = rok_cmd(&home, &root, &["--env", "r"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let input = format!(
        ":add g --path {}\nuse g::greet;\ngreet() + 40\n",
        root.join("lib1").display()
    );
    child
        .stdin
        .take()
        .unwrap()
        .write_all(input.as_bytes())
        .unwrap();
    let out = child.wait_with_output().unwrap();
    let stdout = ok(&out);
    assert!(
        stdout.contains("i32: 41"),
        "{stdout}\n{}",
        text(&out.stderr)
    );
    assert!(read(&home.join("envs/r/rok.rokon")).contains("\"g\": Dep::path("));
}

/// `rok build` builds each dependency once into `target/<profile>/deps`
/// (`lib<name>.a` + `<name>.rhir`), reuses it while nothing it depends
/// on changes, and rebuilds it (and the ones after it) when its source
/// does. A dependency of a dependency is built first.
#[test]
fn prebuilt_dependencies_are_reused_and_rebuilt() {
    if !llvm() {
        return;
    }
    let root = scratch("prebuilt");
    let home = root.join("home");
    write(
        &root.join("base/lib.rok"),
        "pub struct Cell { pub v: i32; }\npub fn cell(v: i32) -> Cell { return Cell { v: v }; }\n",
    );
    write(&root.join("base/rok.rokon"), "Package { name: \"base\" }\n");
    write(
        &root.join("mid/lib.rok"),
        "pub fn twice<T>(x: T) -> (T, T) { return (x, x); }\n\
         pub fn get() -> i32 { return base::cell(20).v + 1; }\n",
    );
    write(
        &root.join("mid/rok.rokon"),
        "Package {\n    name: \"mid\",\n    deps: { \"base\": Dep::path(\"../base\") },\n}\n",
    );
    let app = root.join("app");
    ok(&rok(&home, &root, &["new", "app"]));
    write(
        &app.join("main.rok"),
        "let (a, b) = mid::twice(\"x\");\nprintln(f\"{mid::get()} {a}{b}\");\n",
    );
    write(
        &app.join("rok.rokon"),
        "Package {\n    name: \"app\",\n    deps: { \"mid\": Dep::path(\"../mid\") },\n}\n",
    );
    let built = |out: &Output, dep: &str| text(&out.stderr).contains(&format!("Compiling {dep} "));
    let out = rok(&home, &app, &["run"]);
    assert_eq!(ok(&out), "21 xx\n");
    assert!(
        built(&out, "base") && built(&out, "mid"),
        "{}",
        text(&out.stderr)
    );
    let deps = app.join("target/debug/deps");
    for f in ["libbase.a", "base.rhir", "libmid.a", "mid.rhir"] {
        assert!(deps.join(f).is_file(), "{f}");
    }
    // Nothing changed: both reused.
    let out = rok(&home, &app, &["run"]);
    assert_eq!(ok(&out), "21 xx\n");
    assert!(
        !built(&out, "base") && !built(&out, "mid"),
        "{}",
        text(&out.stderr)
    );
    // `base` changed: it and `mid` (built after it) are rebuilt.
    write(
        &root.join("base/lib.rok"),
        "pub struct Cell { pub v: i32; }\npub fn cell(v: i32) -> Cell { return Cell { v: v * 2 }; }\n",
    );
    let out = rok(&home, &app, &["run"]);
    assert_eq!(ok(&out), "41 xx\n");
    assert!(
        built(&out, "base") && built(&out, "mid"),
        "{}",
        text(&out.stderr)
    );
    // Another profile is another build.
    let out = rok(&home, &app, &["build", "--release"]);
    ok(&out);
    assert!(built(&out, "mid"), "{}", text(&out.stderr));
    assert!(app.join("target/release/deps/mid.rhir").is_file());
}

#[test]
fn rokls_is_rok_lsp() {
    let root = scratch("lsp");
    let frame = |b: &str| format!("Content-Length: {}\r\n\r\n{b}", b.len());
    let input = [
        r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"capabilities":{}}}"#,
        r#"{"jsonrpc":"2.0","id":2,"method":"shutdown"}"#,
        r#"{"jsonrpc":"2.0","method":"exit"}"#,
    ]
    .map(frame)
    .concat();
    build_rokc();
    for (exe, args) in [(env!("CARGO_BIN_EXE_rokls"), &[][..]), (ROK, &["lsp"][..])] {
        let mut child = Command::new(exe)
            .args(args)
            .current_dir(&root)
            .env("ROK_HOME", root.join("home"))
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        child
            .stdin
            .take()
            .unwrap()
            .write_all(input.as_bytes())
            .unwrap();
        let out = child.wait_with_output().unwrap();
        let stdout = ok(&out);
        assert!(stdout.contains(r#""hoverProvider":true"#), "{stdout}");
    }
}

const ONE: &str = "pub fn one() -> i32 { return 1; }\n";

/// A stone's repository at `dir`: `files` plus a `rok.rokon` for `name`
/// `vers` with `deps`, committed, with itself as remote `origin`.
fn stone(dir: &Path, name: &str, vers: &str, deps: &str, files: &[(&str, &str)]) -> String {
    stone_meta(dir, name, vers, deps, "", files)
}

/// `stone` with manifest fields `meta` (`license: "MIT", `).
fn stone_meta(
    dir: &Path,
    name: &str,
    vers: &str,
    deps: &str,
    meta: &str,
    files: &[(&str, &str)],
) -> String {
    let manifest =
        format!("Package {{ name: \"{name}\", version: \"{vers}\", {meta}deps: {{ {deps} }} }}\n");
    let mut all = files.to_vec();
    all.push(("rok.rokon", &manifest));
    let c = commit(dir, &all);
    if git(dir, &["remote"]).is_empty() {
        git(
            dir,
            &["remote", "add", "origin", &dir.display().to_string()],
        );
    }
    c
}

/// `name` / `vers` pairs of the stones in `rok.lock`.
fn locked_stones(lock: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut name = "";
    for l in lock.lines().map(str::trim) {
        if let Some(n) = l.strip_prefix("name: ") {
            name = n.trim_end_matches(',');
        } else if let Some(v) = l.strip_prefix("vers: ") {
            out.push(format!(
                "{}@{}",
                name.trim_matches('"'),
                v.trim_end_matches(',').trim_matches('"')
            ));
        }
    }
    out
}

/// Publish `num` 1.0.0, 1.1.0, 2.0.0 and `geom` 0.3.0 (needing `num`
/// ^1.0) to the index checkout `index`, checking `publish` on the way;
/// `num` 1.0.0's tree.
fn publish_stones(root: &Path, home: &Path, index: &Path) -> String {
    let reg = index.display().to_string();
    let index_log = || git(index, &["log", "--format=%s"]);
    let one = ONE;
    // `num` 1.0.0: a dry run prints the line and writes nothing.
    let num = root.join("num");
    let c1 = stone(&num, "num", "1.0.0", "", &[("lib.rok", one)]);
    let tree1 = git(&num, &["rev-parse", "HEAD^{tree}"]);
    let line = format!(
        "Stone {{ name: \"num\", vers: \"1.0.0\", deps: [], source: Dep::git(\"{}\", rev: \
         \"{c1}\"), cksum: \"{tree1}\", yanked: false }}\n",
        num.display()
    );
    assert_eq!(ok(&rok(home, &num, &["publish"])), line);
    assert_eq!(ok(&rok(home, &num, &["publish", "--index", &reg])), line);
    assert!(!index.join("3/n/num").exists());
    fails(
        &rok(home, &num, &["publish", "--commit"]),
        "--commit needs --index",
    );
    ok(&rok(home, &num, &["publish", "--index", &reg, "--commit"]));
    assert_eq!(read(&index.join("3/n/num")), line);
    assert!(
        index_log().starts_with("Publish num 1.0.0\n"),
        "{}",
        index_log()
    );
    fails(
        &rok(home, &num, &["publish", "--index", &reg, "--commit"]),
        "num 1.0.0 is already in the index",
    );
    write(&num.join("lib.rok"), "dirty");
    fails(&rok(home, &num, &["publish"]), "uncommitted changes");

    // More versions, and `geom` 0.3.0 needing `num` ^1.0.
    for v in ["1.1.0", "2.0.0"] {
        stone(&num, "num", v, "", &[("lib.rok", one)]);
        ok(&rok(home, &num, &["publish", "--index", &reg, "--commit"]));
    }
    let geom = root.join("geom");
    let two = "use num::one;\npub fn two() -> i32 { return one() + one(); }\n";
    // Manifest metadata rides along in the entry.
    stone_meta(
        &geom,
        "geom",
        "0.3.0",
        "\"num\": \"^1.0\"",
        "description: \"Shapes\", license: \"MIT\", repository: \"https://example.com/geom\", ",
        &[("lib.rok", two)],
    );
    ok(&rok(home, &geom, &["publish", "--index", &reg, "--commit"]));
    let entry = read(&index.join("ge/om/geom"));
    assert!(
        entry.contains("deps: [{ name: \"num\", req: \"^1.0\", kind: \"normal\" }]"),
        "{entry}"
    );
    assert!(
        entry.contains(
            "yanked: false, description: \"Shapes\", license: \"MIT\", repository: \
             \"https://example.com/geom\" }"
        ),
        "{entry}"
    );
    // A path dependency cannot be published.
    let bad = root.join("bad");
    stone(
        &bad,
        "bad",
        "0.1.0",
        "\"x\": Dep::path(\"..\")",
        &[("lib.rok", one)],
    );
    fails(
        &rok(home, &bad, &["publish"]),
        "dependency `x` is not a stone",
    );

    tree1
}

/// Stones end to end on a local index: publish (dry run and commit),
/// `add` / lock / `update`, conflicts, yank, cksum checks, search.
#[test]
fn stones_publish_add_update_yank() {
    let root = scratch("stones");
    let home = root.join("home");
    let index = root.join("index");
    commit(
        &index,
        &[(
            "config.rokon",
            "Registry { name: \"test\", dl: \"git\", api: \"https://rokstones.io\" }\n",
        )],
    );
    for kv in [
        ["user.name", "t"],
        ["user.email", "t@t"],
        ["commit.gpgsign", "false"],
    ] {
        git(&index, &["config", kv[0], kv[1]]);
    }
    let reg = index.display().to_string();
    write(
        &home.join("config.rokon"),
        &format!("Config {{ registry: \"{reg}\" }}\n"),
    );
    let num = root.join("num");
    let tree1 = publish_stones(&root, &home, &index);
    let index_log = || git(&index, &["log", "--format=%s"]);

    // `add`: `^` the newest version; the lock pins both stones.
    let app = root.join("app");
    write(
        &app.join("main.rok"),
        "use geom::two;\nprintln(f\"{two()}\");\n",
    );
    write(&app.join("rok.rokon"), APP0);
    ok(&rok(&home, &app, &["add", "geom"]));
    assert!(read(&app.join("rok.rokon")).contains("\"geom\": Dep::version(\"^0.3.0\"),"));
    let lock = read(&app.join("rok.lock"));
    assert_eq!(locked_stones(&lock), ["geom@0.3.0", "num@1.1.0"]);
    assert!(
        lock.contains("source: Dep::registry(") && lock.contains(&format!("\"{reg}\"")),
        "{lock}"
    );
    let names: Vec<String> = deps(&home, &app, &[]).into_iter().map(|(n, _)| n).collect();
    assert_eq!(names, ["num", "geom"]);
    if llvm() {
        assert_eq!(ok(&rok(&home, &app, &["-q", "run"])), "2\n");
    }

    // A root requirement the chosen version does not meet: a conflict
    // naming both, and rok.rokon as it was.
    let before = read(&app.join("rok.rokon"));
    let out = rok(&home, &app, &["add", "num@2"]);
    fails(&out, "conflicting requirements for stone `num`");
    for want in [
        "`2` (required by the root package)",
        "`^1.0` (required by `geom`)",
    ] {
        assert!(text(&out.stderr).contains(want), "{}", text(&out.stderr));
    }
    assert_eq!(read(&app.join("rok.rokon")), before);
    ok(&rok(&home, &app, &["add", "num@~1.1"]));
    assert!(read(&app.join("rok.rokon")).contains("\"num\": Dep::version(\"~1.1\"),"));
    fails(
        &rok(&home, &app, &["add", "num@^9"]),
        "no version of stone `num` matches `^9`",
    );
    fails(&rok(&home, &app, &["add", "nope"]), "no stone named `nope`");
    fails(
        &rok(&home, &app, &["add", "num@x.y"]),
        "is not a version requirement",
    );

    // A new version: builds keep the locked one until `update`.
    stone(&num, "num", "1.1.5", "", &[("lib.rok", ONE)]);
    ok(&rok(&home, &num, &["publish", "--index", &reg, "--commit"]));
    ok(&rok(&home, &app, &["--locked", "deps"]));
    assert!(locked_stones(&read(&app.join("rok.lock"))).contains(&"num@1.1.0".to_owned()));
    ok(&rok(&home, &app, &["update", "num"]));
    assert!(locked_stones(&read(&app.join("rok.lock"))).contains(&"num@1.1.5".to_owned()));
    ok(&rok(&home, &app, &["--offline", "deps"]));

    // Yanked: kept while locked, skipped by `update`; `--undo` restores.
    ok(&rok(
        &home,
        &num,
        &["yank", "--vers", "1.1.5", "--index", &reg],
    ));
    assert!(read(&index.join("3/n/num")).contains("vers: \"1.1.5\""));
    assert!(index_log().starts_with("Yank num 1.1.5\n"));
    ok(&rok(&home, &app, &["deps"]));
    assert!(locked_stones(&read(&app.join("rok.lock"))).contains(&"num@1.1.5".to_owned()));
    ok(&rok(&home, &app, &["update"]));
    assert!(locked_stones(&read(&app.join("rok.lock"))).contains(&"num@1.1.0".to_owned()));
    let out = rok(&home, &app, &["add", "num@=1.1.5"]);
    fails(&out, "1.1.5 (yanked)");
    ok(&rok(
        &home,
        &num,
        &["yank", "--undo", "--vers", "1.1.5", "--index", &reg, "num"],
    ));
    ok(&rok(&home, &app, &["add", "num@=1.1.5"]));
    fails(
        &rok(&home, &num, &["yank", "--vers", "9.9.9", "--index", &reg]),
        "not in the index",
    );

    // An entry whose cksum is not its commit's tree is refused.
    let entry = read(&index.join("3/n/num"))
        .lines()
        .next()
        .unwrap()
        .replace("1.0.0", "1.0.1");
    let forged = format!("{}\n", entry.replace(&tree1, &"0".repeat(40)));
    write(
        &index.join("3/n/num"),
        &(read(&index.join("3/n/num")) + &forged),
    );
    git(&index, &["commit", "-qam", "forged"]);
    fails(
        &rok(&home, &app, &["add", "num@=1.0.1"]),
        "but the index's cksum is",
    );

    // `search`, with the index from ROK_REGISTRY in a fresh ROK_HOME.
    let home2 = root.join("home2");
    let out = rok_cmd(&home2, &root, &["search", "o"])
        .env("ROK_REGISTRY", &reg)
        .output()
        .unwrap();
    assert_eq!(ok(&out), "geom = \"0.3.0\"\n");
    assert_eq!(
        ok(&rok(&home, &root, &["search", "NU"])),
        "num = \"2.0.0\"\n"
    );

    // A per-dependency index.
    ok(&rok(&home, &app, &["add", "geom@0.3", "--registry", &reg]));
    assert!(read(&app.join("rok.rokon")).contains(&format!(
        "\"geom\": Dep::version(\"0.3\", registry: \"{reg}\"),"
    )));
}
