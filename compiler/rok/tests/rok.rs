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
    write(
        &app.join("Rok.toml"),
        "# my app\n[package]\nname = \"app\"  # keep\n\n[deps]\n# deps go here\n",
    );

    ok(&rok(&home, &app, &["add", "greet", "--git", &url]));
    let manifest = read(&app.join("Rok.toml"));
    assert_eq!(
        manifest,
        format!(
            "# my app\n[package]\nname = \"app\"  # keep\n\n[deps]\n# deps go here\n\
             greet = {{ git = \"{url}\" }}\n"
        )
    );
    let lock = read(&app.join("Rok.lock"));
    let tree = git(&repo, &["rev-parse", "HEAD^{tree}"]);
    assert_eq!(
        lock,
        format!(
            "# Rok.lock: generated by `rok`; do not edit. Commit it with your sources.\n\
             version = 1\n\n[[package]]\nname = \"greet\"\ngit = \"{url}\"\n\
             commit = \"{c1}\"\ntree = \"{tree}\"\n"
        )
    );
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
    assert!(read(&app.join("Rok.lock")).contains(&c2));
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
    write(
        &app.join("Rok.toml"),
        &read(&app.join("Rok.toml")).replace("[deps]", "[deps]\nother = { git = \"/nope\" }"),
    );
    fails(&rok(&home, &app, &["--locked", "deps"]), "--locked");
    write(
        &app.join("Rok.toml"),
        &read(&app.join("Rok.toml")).replace("other = { git = \"/nope\" }\n", ""),
    );

    // A tag; `remove` edits the file and prunes the lock.
    git(&repo, &["tag", "v1", &c1]);
    ok(&rok(
        &home,
        &app,
        &["add", "greet", "--git", &url, "--tag", "v1"],
    ));
    assert!(
        read(&app.join("Rok.toml"))
            .contains(&format!("greet = {{ git = \"{url}\", tag = \"v1\" }}"))
    );
    assert!(read(&app.join("Rok.lock")).contains(&format!("tag = \"v1\"\ncommit = \"{c1}\"")));
    ok(&rok(&home, &app, &["remove", "greet"]));
    assert_eq!(
        read(&app.join("Rok.toml")),
        "# my app\n[package]\nname = \"app\"  # keep\n\n[deps]\n# deps go here\n"
    );
    assert!(!read(&app.join("Rok.lock")).contains("[[package]]"));
    fails(&rok(&home, &app, &["remove", "greet"]), "not a dependency");

    // A bad source leaves Rok.toml as it was.
    let before = read(&app.join("Rok.toml"));
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
    assert_eq!(read(&app.join("Rok.toml")), before);
    fails(
        &rok(&home, &app, &["add", "my-x", "--path", "."]),
        "try `my_x`",
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
                "Rok.toml",
                &format!(
                    "[package]\nname = \"a\"\n[deps]\nb = {{ git = \"{}\" }}\n",
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
    assert_eq!(names, ["a", "b"]);
    let lock = read(&app.join("Rok.lock"));
    assert!(
        lock.contains("name = \"a\"") && lock.contains("name = \"b\""),
        "{lock}"
    );

    // `b` from a path as well: two packages named `b`.
    let other_b = root.join("other_b");
    write(
        &other_b.join("lib.rok"),
        "pub fn b() -> i32 { return 3; }\n",
    );
    let before = read(&app.join("Rok.toml"));
    fails(
        &rok(&home, &app, &["add", "b", "--path", "../other_b"]),
        "conflicting requirements for package `b`",
    );
    assert_eq!(read(&app.join("Rok.toml")), before);

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
    assert!(read(&app.join("Rok.toml")).contains("[dev-deps]\nc = { path = \"../other_b\" }\n"));
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
    write(&app.join("Rok.toml"), "[deps]\nfoo = \"1.0\"\n");
    let out = rok(&home, &app, &["deps"]);
    fails(&out, "registry dependencies are not supported yet");
    assert!(
        text(&out.stderr).contains("Rok.toml:2:7"),
        "{}",
        text(&out.stderr)
    );
    write(&app.join("Rok.toml"), "[deps]\nfoo = { native = \"z\" }\n");
    fails(
        &rok(&home, &app, &["deps"]),
        "reserved and not supported yet",
    );
    write(&app.join("Rok.toml"), "[deps\n");
    fails(
        &rok(&home, &app, &["deps"]),
        "Rok.toml:1:6: error: expected `]`",
    );

    // A wrongly cased manifest is ignored with a warning.
    fs::remove_file(app.join("Rok.toml")).unwrap();
    write(&app.join("rok.toml"), "[deps]\n");
    let out = rok(&home, &app, &["deps"]);
    ok(&out);
    assert!(
        text(&out.stderr).contains("the manifest is named `Rok.toml`"),
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
        read(&root.join("mylib/Rok.toml")),
        "[package]\nname = \"mylib\"\nversion = \"0.1.0\"\n\n[deps]\n"
    );
    let dir = root.join("existing");
    fs::create_dir_all(&dir).unwrap();
    ok(&rok(&home, &dir, &["init"]));
    assert!(dir.join("main.rok").is_file() && dir.join("Rok.toml").is_file());
    fails(&rok(&home, &dir, &["init"]), "already exists");
    assert_eq!(
        ok(&rok(&home, &dir, &["--version"])),
        format!("rok {}\n", env!("CARGO_PKG_VERSION"))
    );
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
        &app.join("Rok.toml"),
        "[package]\nname = \"app\"\n\n[deps]\nutil = { path = \"../util\" }\n\n\
         [lints]\nunused_variables = \"deny\"\n",
    );
    write(
        &app.join("main.rok"),
        "use util::hello;\nlet x = hello();\nprintln(\"hi\");\n",
    );
    // `[lints]` sets the level, the command line overrides it, and the
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
    assert!(text(&out.stderr).contains("warning: [lint]"));
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
        read(&home.join("envs/work/Rok.toml"))
            .contains(&format!("greet = {{ path = \"{}\" }}", lib.display()))
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
    assert!(export.join("Rok.toml").is_file());
    ok(&rok(&home, &root, &["env", "import", "copy", "export"]));
    assert_eq!(deps(&home, &elsewhere, &["--env", "copy"])[0].0, "greet");
    // Import from a project: relative paths become absolute.
    let proj = root.join("proj");
    write(&proj.join("main.rok"), "println(\"p\");\n");
    write(
        &proj.join("Rok.toml"),
        "[deps]\ng = { path = \"../lib1\" }\n",
    );
    ok(&rok(&home, &root, &["env", "import", "fromproj", "proj"]));
    assert!(read(&home.join("envs/fromproj/Rok.toml")).contains(&lib.display().to_string()));

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

#[test]
fn pinned_toolchains() {
    let root = scratch("toolchain");
    let home = root.join("home");
    let app = root.join("app");
    write(&app.join("main.rok"), "println(\"x\");\n");
    write(&app.join("Rok.toml"), "[package]\ntoolchain = \"9.9\"\n");
    fails(&rok(&home, &app, &["build"]), "rok toolchain install 9.9");

    // A fake toolchain whose rokc reports how it was called.
    let fake = root.join("fake");
    write(
        &fake.join("bin/rokc"),
        "#!/bin/sh\necho \"fake rokc ROK_HOME=$ROK_HOME $*\"\n",
    );
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(fake.join("bin/rokc"), fs::Permissions::from_mode(0o755)).unwrap();
    }
    fails(
        &rok(&home, &root, &["toolchain", "install", "9.9.1"]),
        "no toolchain download server",
    );
    fails(
        &rok(
            &home,
            &root,
            &["toolchain", "install", "9.9.1", "--from", "app"],
        ),
        "no bin/rokc",
    );
    ok(&rok(
        &home,
        &root,
        &["toolchain", "install", "9.9.1", "--from", "fake"],
    ));
    let out = ok(&rok(&home, &app, &["-q", "build", "--release"]));
    let tc = home.join("toolchains/9.9.1");
    assert_eq!(
        out,
        format!("fake rokc ROK_HOME={} -q build --release\n", tc.display())
    );

    // From a tarball with one top directory.
    let ok_tar = Command::new("tar")
        .current_dir(&root)
        .args(["-czf", "tc.tar.gz", "fake"])
        .status()
        .unwrap()
        .success();
    assert!(ok_tar);
    ok(&rok(
        &home,
        &root,
        &["toolchain", "install", "9.10", "--from", "tc.tar.gz"],
    ));
    assert!(home.join("toolchains/9.10/bin/rokc").is_file());
    let list = ok(&rok(&home, &root, &["toolchain", "list"]));
    assert!(list.ends_with("9.9.1\n9.10\n"), "{list}");
    ok(&rok(&home, &root, &["toolchain", "remove", "9.9.1"]));
    fails(&rok(&home, &app, &["build"]), "is not installed");
    // Pinning this rok's own version runs the rokc beside it.
    let mine: String = env!("CARGO_PKG_VERSION")
        .split('.')
        .take(2)
        .collect::<Vec<_>>()
        .join(".");
    write(
        &app.join("Rok.toml"),
        &format!("[package]\ntoolchain = \"{mine}\"\n"),
    );
    ok(&rok(&home, &app, &["-q", "check"]));
}

#[test]
fn script_dependencies() {
    let root = scratch("script");
    let home = root.join("home");
    write(&root.join("lib1/lib.rok"), LIB_V1);
    let script = "//! ```toml\n//! [deps]\n//! greet = { path = \"lib1\" }\n//! ```\n\
                  use greet::greet;\nprintln(f\"{greet()}\");\n";
    write(&root.join("s.rok"), script);
    ok(&rok(&home, &root, &["-q", "check", "s.rok"]));
    // Its lock lives in the cache, not next to the script.
    assert!(!root.join("Rok.lock").exists());
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
        "//! ```toml\n//! [deps]\n//! g = 1\n//! ```\n",
    );
    fails(
        &rok(&home, &root, &["check", "bad.rok"]),
        "bad.rok (//! toml block):2:5",
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
    assert!(read(&home.join("envs/r/Rok.toml")).contains("g = { path"));
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
    write(&root.join("base/Rok.toml"), "[package]\nname = \"base\"\n");
    write(
        &root.join("mid/lib.rok"),
        "pub fn twice<T>(x: T) -> (T, T) { return (x, x); }\n\
         pub fn get() -> i32 { return base::cell(20).v + 1; }\n",
    );
    write(
        &root.join("mid/Rok.toml"),
        "[package]\nname = \"mid\"\n\n[deps]\nbase = { path = \"../base\" }\n",
    );
    let app = root.join("app");
    ok(&rok(&home, &root, &["new", "app"]));
    write(
        &app.join("main.rok"),
        "let (a, b) = mid::twice(\"x\");\nprintln(f\"{mid::get()} {a}{b}\");\n",
    );
    write(
        &app.join("Rok.toml"),
        "[package]\nname = \"app\"\n\n[deps]\nmid = { path = \"../mid\" }\n",
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
