//! `rokc test` (spec 901): run each selected `#[test]` function in its
//! own process (the harness binary takes the test name as `argv[1]`), so
//! a panic or an escaping error fails only that test.

use std::path::Path;
use std::process::{Command, Output};
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

pub struct Options<'a> {
    pub filter: Option<&'a str>,
    pub threads: usize,
    pub show_output: bool,
}

/// Run `tests` from the harness `exe`; prints a cargo-style report to
/// stdout and returns whether every test passed.
pub fn run(exe: &Path, tests: &[String], opts: &Options<'_>) -> bool {
    let started = Instant::now();
    let selected: Vec<&String> = tests
        .iter()
        .filter(|t| opts.filter.is_none_or(|f| re_match(f, t)))
        .collect();
    let filtered_out = tests.len() - selected.len();
    println!(
        "\nrunning {} test{}",
        selected.len(),
        if selected.len() == 1 { "" } else { "s" }
    );

    let next = AtomicUsize::new(0);
    let results: Mutex<Vec<(&String, Result<Output, String>)>> = Mutex::new(Vec::new());
    std::thread::scope(|s| {
        for _ in 0..opts.threads.clamp(1, selected.len().max(1)) {
            s.spawn(|| {
                while let Some(&name) = selected.get(next.fetch_add(1, Ordering::Relaxed)) {
                    let out = Command::new(exe)
                        .arg(name)
                        .output()
                        .map_err(|e| format!("cannot run {}: {e}", exe.display()));
                    let ok = out.as_ref().is_ok_and(|o| o.status.success());
                    println!("test {name} ... {}", if ok { "ok" } else { "FAILED" });
                    results
                        .lock()
                        .unwrap_or_else(std::sync::PoisonError::into_inner)
                        .push((name, out));
                }
            });
        }
    });
    let mut results = results
        .into_inner()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    results.sort_by_key(|(n, _)| *n);

    let passed = |r: &Result<Output, String>| r.as_ref().is_ok_and(|o| o.status.success());
    let failed: Vec<_> = results.iter().filter(|(_, r)| !passed(r)).collect();
    if opts.show_output {
        let ok: Vec<_> = results.iter().filter(|(_, r)| passed(r)).collect();
        section("successes", &ok);
    }
    section("failures", &failed);
    println!(
        "\ntest result: {}. {} passed; {} failed; {filtered_out} filtered out; finished in {:.2}s\n",
        if failed.is_empty() { "ok" } else { "FAILED" },
        results.len() - failed.len(),
        failed.len(),
        started.elapsed().as_secs_f64()
    );
    failed.is_empty()
}

fn section(title: &str, rows: &[&(&String, Result<Output, String>)]) {
    if rows.is_empty() {
        return;
    }
    println!("\n{title}:");
    for (name, r) in rows {
        println!("\n---- {name} ----");
        match r {
            Ok(o) => {
                print!("{}", String::from_utf8_lossy(&o.stdout));
                print!("{}", String::from_utf8_lossy(&o.stderr));
                if !o.status.success() {
                    println!("({})", describe(o));
                }
            }
            Err(e) => println!("{e}"),
        }
    }
    println!("\n{title}:");
    for (name, _) in rows {
        println!("    {name}");
    }
}

fn describe(o: &Output) -> String {
    #[cfg(unix)]
    if let Some(sig) = std::os::unix::process::ExitStatusExt::signal(&o.status) {
        return format!("killed by signal {sig}");
    }
    match o.status.code() {
        Some(101) => "panicked (exit 101)".to_owned(),
        Some(c) => format!("exit {c}"),
        None => "no exit code".to_owned(),
    }
}

/// The test filter (spec 901: "regex or plain substring"): unanchored
/// match supporting `^ $ . * + ?` and `\` escapes; a filter without
/// those is a substring search. ponytail: no classes / groups /
/// alternation; add them if filters need them.
pub fn re_match(re: &str, text: &str) -> bool {
    let re: Vec<char> = re.chars().collect();
    let text: Vec<char> = text.chars().collect();
    if re.first() == Some(&'^') {
        return here(&re[1..], &text);
    }
    (0..=text.len()).any(|i| here(&re, &text[i..]))
}

fn here(re: &[char], t: &[char]) -> bool {
    let Some(&c) = re.first() else { return true };
    if c == '$' && re.len() == 1 {
        return t.is_empty();
    }
    let (atom, len) = match (c, re.get(1)) {
        ('\\', Some(&l)) => (Some(l), 2),
        ('.', _) => (None, 1),
        _ => (Some(c), 1),
    };
    let hit = |t: &[char]| t.first().is_some_and(|&x| atom.is_none_or(|a| a == x));
    let rest = &re[len..];
    match rest.first() {
        Some('*') => star(hit, &rest[1..], t),
        Some('+') => hit(t) && star(hit, &rest[1..], &t[1..]),
        Some('?') => here(&rest[1..], t) || (hit(t) && here(&rest[1..], &t[1..])),
        _ => hit(t) && here(rest, &t[1..]),
    }
}

fn star(hit: impl Fn(&[char]) -> bool, re: &[char], mut t: &[char]) -> bool {
    loop {
        if here(re, t) {
            return true;
        }
        if !hit(t) {
            return false;
        }
        t = &t[1..];
    }
}

#[cfg(test)]
mod tests {
    use super::re_match;

    #[test]
    fn filter_regex() {
        assert!(re_match("add", "math::adds"));
        assert!(!re_match("sub", "math::adds"));
        assert!(re_match("^math::", "math::adds"));
        assert!(!re_match("^adds", "math::adds"));
        assert!(re_match("s$", "math::adds"));
        assert!(re_match("a.*d", "math::adds"));
        assert!(re_match("ad+s", "math::adds"));
        assert!(re_match("^x?math", "math::adds"));
        assert!(re_match("a\\.b", "a.b"));
        assert!(!re_match("a\\.b", "axb"));
    }
}
