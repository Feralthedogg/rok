#!/usr/bin/env python3
"""Benchmark runner: see bench/README.md.

Builds bench/*.rok at -O2 (release rokc + runtime) and bench/c/*.c with
clang -O2, runs each best-of-N under /usr/bin/time, records instructions
retired, user CPU and peak RSS in bench/history.jsonl keyed by the git
commit, and compares against the previous record. Exit 1 when a
benchmark regresses past the threshold (instructions, or user time where
instructions are not available).
"""

import argparse
import datetime
import json
import os
import platform
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BENCH = os.path.join(ROOT, "bench")
OUT = os.path.join(ROOT, "target", "bench")
HISTORY = os.path.join(BENCH, "history.jsonl")
MAC = platform.system() == "Darwin"


def sh(args, **kw):
    return subprocess.run(args, check=True, **kw)


def git(*args):
    r = subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True)
    return r.stdout.strip() if r.returncode == 0 else ""


def build(names):
    """{name: exe} for the rok and C programs whose name matches."""
    sh(["cargo", "build", "--release", "-q", "-p", "rokr", "-p", "rokc"], cwd=ROOT)
    os.makedirs(OUT, exist_ok=True)
    rokc = os.path.join(ROOT, "target", "release", "rokc")
    exes = {}
    for f in sorted(os.listdir(BENCH)):
        name = f[:-4]
        if f.endswith(".rok") and names(name):
            exe = os.path.join(OUT, name)
            r = subprocess.run([rokc, "-q", "build", os.path.join(BENCH, f), "-O2", "-o", exe], cwd=ROOT)
            if r.returncode != 0:
                print(f"BUILD FAILED: {f}", file=sys.stderr)
                continue
            exes[name] = exe
    cdir = os.path.join(BENCH, "c")
    for f in sorted(os.listdir(cdir)):
        name = f[:-2]
        if f.endswith(".c") and names(name):
            exe = os.path.join(OUT, "c_" + name)
            sh(["clang", "-O2", "-o", exe, os.path.join(cdir, f), "-lm"])
            exes["c/" + name] = exe
    return exes


def measure(exe):
    """(stdout, {insns, user, rss_kb}) of one run."""
    if MAC:
        cmd = ["/usr/bin/time", "-l", exe]
    else:
        cmd = ["/usr/bin/time", "-f", "%U user\n%M maxrss", exe]
    r = subprocess.run(cmd, capture_output=True, text=True)
    if r.returncode != 0:
        raise SystemExit(f"{exe} exited {r.returncode}:\n{r.stderr[-2000:]}")
    err = r.stderr
    stats = {}
    m = re.search(r"([\d.]+) user", err)
    stats["user"] = float(m.group(1)) if m else None
    m = re.search(r"(\d+)\s+instructions retired", err)
    stats["insns"] = int(m.group(1)) if m else None
    m = re.search(r"(\d+)\s+maximum resident set size", err) or re.search(r"(\d+) maxrss", err)
    if m:
        # macOS reports bytes, GNU time KiB.
        stats["rss_kb"] = int(m.group(1)) // (1024 if MAC else 1)
    return r.stdout, stats


def best(exe, runs):
    out, best = None, {}
    for _ in range(runs):
        out, s = measure(exe)
        for k, v in s.items():
            if v is not None and (k not in best or v < best[k]):
                best[k] = v
    return out, best


def previous():
    try:
        with open(HISTORY) as f:
            lines = [l for l in f if l.strip()]
        return json.loads(lines[-1]) if lines else None
    except FileNotFoundError:
        return None


def pct(new, old):
    if new is None or not old:
        return None
    return (new - old) * 100.0 / old


def fmt(v, unit=""):
    if v is None:
        return "-"
    if isinstance(v, float):
        return f"{v:.3f}{unit}"
    return f"{v:,}{unit}"


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("filter", nargs="?", default="", help="only benchmarks containing this")
    ap.add_argument("--runs", type=int, default=3, help="best of N (default 3)")
    ap.add_argument("--threshold", type=float, default=3.0, help="regression threshold in %% (default 3)")
    ap.add_argument("--no-record", action="store_true", help="do not append to history.jsonl")
    a = ap.parse_args()

    prev = previous()
    exes = build(lambda n: a.filter in n)
    results, outputs = {}, {}
    for name, exe in exes.items():
        outputs[name], results[name] = best(exe, a.runs)
        print(f"  {name}: {fmt(results[name].get('insns'))} insns, {fmt(results[name].get('user'), 's')} user",
              file=sys.stderr)

    commit = git("rev-parse", "--short=12", "HEAD")
    entry = {
        "commit": commit,
        "dirty": bool(git("status", "--porcelain", "--untracked-files=no")),
        "subject": git("log", "-1", "--format=%s"),
        "date": datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds"),
        "host": f"{platform.system()}-{platform.machine()}",
        "runs": a.runs,
        "results": results,
    }

    base = (prev or {}).get("results", {})
    print(f"\ncommit {commit}{' (dirty)' if entry['dirty'] else ''}"
          + (f" vs {prev['commit']}{' (dirty)' if prev.get('dirty') else ''}" if prev else " (no previous record)"))
    print(f"{'benchmark':<18} {'instructions':>16} {'Δ%':>7} {'user s':>8} {'Δ%':>7} {'rss KiB':>9} {'vs C':>6}")
    regressions, mismatches = [], []
    for name in sorted(results):
        r, o = results[name], base.get(name, {})
        di, du = pct(r.get("insns"), o.get("insns")), pct(r.get("user"), o.get("user"))
        c = results.get("c/" + name)
        ratio = None
        if c and c.get("insns") and r.get("insns"):
            ratio = r["insns"] / c["insns"]
        elif c and c.get("user") and r.get("user"):
            ratio = r["user"] / c["user"]
        if c and outputs.get("c/" + name) != outputs[name]:
            mismatches.append(name)
        key = di if di is not None else du
        flag = ""
        if key is not None and key > a.threshold:
            flag = "  REGRESSION"
            regressions.append(name)
        print(f"{name:<18} {fmt(r.get('insns')):>16} {fmt(di) if di is None else f'{di:+.1f}':>7} "
              f"{fmt(r.get('user')):>8} {fmt(du) if du is None else f'{du:+.1f}':>7} "
              f"{fmt(r.get('rss_kb')):>9} {'' if ratio is None else f'{ratio:.2f}x':>6}{flag}")

    if not a.no_record:
        with open(HISTORY, "a") as f:
            f.write(json.dumps(entry, sort_keys=True) + "\n")
        print(f"\nrecorded in {os.path.relpath(HISTORY, ROOT)}")
    for n in mismatches:
        print(f"OUTPUT MISMATCH: {n} prints differently from c/{n}")
    if regressions:
        print(f"{len(regressions)} regression(s) over {a.threshold}%: {', '.join(regressions)}")
    return 1 if regressions or mismatches else 0


if __name__ == "__main__":
    sys.exit(main())
