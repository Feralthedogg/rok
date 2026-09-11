//! `rokc bench` (spec 901 / 9.9.11): time each selected `#[bench]`
//! function. The harness binary takes `name iters samples` and prints
//! one `#rokbench <ns>` line per sample (see the driver's `harness`), so
//! timing happens inside the process, not around a spawn.
//!
//! Per bench: unless `--iters` fixes it, calibrate the calls per sample
//! by growing it until one sample takes ~10ms; then one process runs a
//! warm-up sample (dropped) and `samples` timed ones. The report is the
//! mean ns per call and the standard deviation across samples:
//!
//! ```text
//! bench fib_20 ... bench:       41,503 ns/iter (+/- 312)
//! ```
//!
//! Benches run one at a time (parallel runs would disturb the timings).
//! There is no `black_box`, so an optimizer may delete a bench body
//! whose result is unused.

use std::path::Path;
use std::process::Command;
use std::time::Instant;

use crate::test_runner::re_match;

pub struct Options<'a> {
    pub filter: Option<&'a str>,
    /// Calls per sample; `None`: calibrate.
    pub iters: Option<u64>,
    pub samples: u64,
}

/// Calibration target for one sample.
const SAMPLE_NS: u64 = 10_000_000;

/// Run `benches` from the harness `exe`, printing a report to stdout;
/// whether every bench ran.
pub fn run(exe: &Path, benches: &[String], opts: &Options<'_>) -> bool {
    let started = Instant::now();
    let selected: Vec<&String> = benches
        .iter()
        .filter(|b| opts.filter.is_none_or(|f| re_match(f, b)))
        .collect();
    println!(
        "\nrunning {} bench{}",
        selected.len(),
        if selected.len() == 1 { "" } else { "es" }
    );
    let width = selected.iter().map(|b| b.len()).max().unwrap_or(0);
    let mut failed = Vec::new();
    for name in &selected {
        match measure(exe, name, opts) {
            Ok((mean, dev)) => println!(
                "bench {name:<width$} ... bench: {:>12} ns/iter (+/- {})",
                thousands(mean),
                thousands(dev)
            ),
            Err(e) => {
                println!("bench {name:<width$} ... FAILED");
                failed.push((name, e));
            }
        }
    }
    if !failed.is_empty() {
        println!("\nfailures:");
        for (name, e) in &failed {
            println!("\n---- {name} ----\n{e}");
        }
    }
    println!(
        "\nbench result: {}. {} measured; {} failed; {} filtered out; finished in {:.2}s\n",
        if failed.is_empty() { "ok" } else { "FAILED" },
        selected.len() - failed.len(),
        failed.len(),
        benches.len() - selected.len(),
        started.elapsed().as_secs_f64()
    );
    failed.is_empty()
}

/// `(mean, standard deviation)` in ns per call.
fn measure(exe: &Path, name: &str, opts: &Options<'_>) -> Result<(f64, f64), String> {
    let iters = match opts.iters {
        Some(n) => n,
        None => calibrate(exe, name)?,
    };
    let s = samples(exe, name, iters, opts.samples + 1)?;
    #[allow(clippy::cast_precision_loss)]
    let per: Vec<f64> = s[1..].iter().map(|&ns| ns as f64 / iters as f64).collect();
    Ok(mean_dev(&per))
}

#[allow(clippy::cast_precision_loss)]
fn mean_dev(xs: &[f64]) -> (f64, f64) {
    let n = xs.len() as f64;
    let mean = xs.iter().sum::<f64>() / n;
    let var = if xs.len() > 1 {
        xs.iter().map(|x| (x - mean).powi(2)).sum::<f64>() / (n - 1.0)
    } else {
        0.0
    };
    (mean, var.sqrt())
}

/// Calls per sample so that one sample takes about `SAMPLE_NS`.
fn calibrate(exe: &Path, name: &str) -> Result<u64, String> {
    let mut iters = 1u64;
    loop {
        let ns = samples(exe, name, iters, 1)?[0];
        if ns >= SAMPLE_NS || iters >= 1 << 32 {
            return Ok(iters);
        }
        let want = iters.saturating_mul(SAMPLE_NS) / ns.max(1);
        iters = want.clamp(iters + 1, iters.saturating_mul(100));
    }
}

/// One harness run: `n` samples of `iters` calls, in ns.
fn samples(exe: &Path, name: &str, iters: u64, n: u64) -> Result<Vec<u64>, String> {
    let out = Command::new(exe)
        .args([name, &iters.to_string(), &n.to_string()])
        .output()
        .map_err(|e| format!("cannot run {}: {e}", exe.display()))?;
    let stdout = String::from_utf8_lossy(&out.stdout);
    if !out.status.success() {
        return Err(format!(
            "{stdout}{}(exit {})",
            String::from_utf8_lossy(&out.stderr),
            out.status
                .code()
                .map_or_else(|| "by signal".to_owned(), |c| c.to_string())
        ));
    }
    let got: Vec<u64> = stdout
        .lines()
        .filter_map(|l| l.strip_prefix("#rokbench ")?.trim().parse().ok())
        .collect();
    if u64::try_from(got.len()).ok() != Some(n) {
        return Err(format!(
            "expected {n} samples from the harness, got:\n{stdout}"
        ));
    }
    Ok(got)
}

/// `12,345` (rounded).
fn thousands(x: f64) -> String {
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    let digits = (x.max(0.0).round() as u64).to_string();
    let mut out = String::new();
    for (i, c) in digits.chars().enumerate() {
        if i > 0 && (digits.len() - i) % 3 == 0 {
            out.push(',');
        }
        out.push(c);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn formatting_and_stats() {
        assert_eq!(thousands(1_234_567.4), "1,234,567");
        assert_eq!(thousands(999.6), "1,000");
        assert_eq!(thousands(12.0), "12");
        let (m, d) = mean_dev(&[1.0, 2.0, 3.0]);
        assert!((m - 2.0).abs() < 1e-9 && (d - 1.0).abs() < 1e-9);
        assert_eq!(mean_dev(&[5.0]), (5.0, 0.0));
    }
}
