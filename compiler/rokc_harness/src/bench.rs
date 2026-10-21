//! The `rok bench` runner (spec 9.1).
//!
//! Each benchmark runs in its own process with inherited stdout, so the
//! library builds a `rok::core::bench::Bench` from the arguments and the
//! measured code prints itself: calibration, sampling, statistics and
//! formatting all live in the library. This runner only selects the
//! benchmarks, passes the sampling options and the terminal width, and
//! reports which ran. Its own lines go to `out`.

use std::io::{IsTerminal, Write};
use std::path::Path;
use std::process::Command;
use std::time::Instant;

use crate::re_match;

pub struct Options<'a> {
    pub filter: Option<&'a str>,
    /// Calls per sample; `None`: the library calibrates (passed as 0).
    pub iters: Option<u64>,
    pub samples: u64,
}

/// Run `benches` from `exe`, each in its own process with inherited stdout
/// so the library prints directly; whether all ran. The runner's own lines
/// go to `out`.
pub fn run(exe: &Path, benches: &[String], opts: &Options<'_>, out: &mut dyn Write) -> bool {
    let started = Instant::now();
    let selected: Vec<&String> = benches
        .iter()
        .filter(|b| opts.filter.is_none_or(|f| re_match(f, b)))
        .collect();
    let tty = std::io::stdout().is_terminal();
    let width = selected.iter().map(|b| b.len()).max().unwrap_or(0);
    let _ = writeln!(
        out,
        "\nbenchmarking {} bench{}",
        selected.len(),
        if selected.len() == 1 { "" } else { "es" }
    );
    let iters = opts.iters.unwrap_or(0).to_string();
    let samples = opts.samples.to_string();
    let width_s = width.to_string();
    let mut failed = 0usize;
    for name in &selected {
        // The child inherits stdout; flush ours so lines stay in order.
        let _ = out.flush();
        let status = Command::new(exe)
            .args([
                name.as_str(),
                iters.as_str(),
                samples.as_str(),
                if tty { "1" } else { "0" },
                width_s.as_str(),
            ])
            .status();
        let ok = match status {
            Ok(s) if s.success() => true,
            Ok(s) => {
                let how = s
                    .code()
                    .map_or_else(|| "signal".to_owned(), |c| format!("exit {c}"));
                let _ = writeln!(out, "  {name:<width$}  FAILED ({how})");
                false
            }
            Err(e) => {
                let _ = writeln!(out, "  {name:<width$}  FAILED ({e})");
                false
            }
        };
        if !ok {
            failed += 1;
        }
    }
    let _ = writeln!(
        out,
        "\nbench result: {}. {} run; {failed} failed; {} filtered out; finished in {:.2}s\n",
        if failed == 0 { "ok" } else { "FAILED" },
        selected.len() - failed,
        benches.len() - selected.len(),
        started.elapsed().as_secs_f64()
    );
    failed == 0
}
