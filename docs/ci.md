# CI

`.github/workflows/ci.yml` (GitHub Actions). Changes to Markdown files alone run nothing; a newer run of the
same branch and event cancels the older one.

## Tiers

| Event | Hosts | Jobs |
|---|---|---|
| push to a branch but `main`, pull request | linux-x64 | `check`, `corpus` at `-O0` |
| push to `main`, merge queue (`merge_group`) | linux-x64, linux-arm64, windows-x64 | `check`, `corpus` at `-O0` |
| nightly (`schedule`, 03:17 UTC), manual run | every host | `check`, `corpus` at `-O0` and `-O2`, `cross-link`, `cross`, `wasm`, `bindgen`, `dist` |

A manual run (`workflow_dispatch`) takes `hosts` (all, or some of `linux-x64 linux-arm64 macos-arm64 macos-x64
windows-x64 windows-arm64`), `jobs` (all, or some of `gate cross wasm bindgen dist`; `none`: prefixes only) and `filter`
(`ROK_TEST_FILTER`: the integration cases to run; the differential suites always run). Hosts: `ubuntu-24.04` x86_64, `ubuntu-24.04-arm` aarch64, `macos-26`
arm64, `macos-26-intel` x86_64, `windows-2022` x86_64, `windows-11-arm` aarch64 (cross only).

## Jobs

- `llvm`, per host: the pinned LLVM prefix (`.github/actions/llvm-prefix`), built by `llvm/build.sh` (Windows
  `llvm/build.ps1`) only when none exists for the hash of the build script and its PGO profile, then stripped
  of what `rokc_llvm` does not link. A GitHub-hosted runner keeps it in the actions cache (120-175 MB per
  host; an entry made on a branch serves that branch only, so the first push to `main` builds every host
  once). On a private repository's standard runners a build took 0.5 h (macOS arm64), 2.2 h (macOS x86_64,
  Linux aarch64), 4.5 h (Linux x86_64) and 6.0 h (Windows: at the 6 h job limit). Linux needs clang 19+ to
  read `rok.profdata.xz`; a build without PGO fails. Windows builds with the pinned release's clang-cl
  (22.1.8: `clang-cl.exe` and its resource headers, ~140 MB, unpacked into the runner's temp directory; its
  version is part of the cache key), which reads `rok-msvc.profdata.tar.xz`; a build without PGO fails there
  too (`cl` reads no clang profile; llvm/README.md).
- `check`, per host: fmt, clippy, every test but the two corpora (`-- --exact --skip end_to_end_cases --skip
  differential`), `rokc fmt --check library`, and the compiler / runtime crate isolation check; every step
  runs even after one fails. On Linux after `targets/build.sh <host>`.
- `corpus`, per host, level and shard: `cargo test --test integration --test differential` with
  `ROK_TEST_SHARD=i/4`. A shard takes every fourth integration case of the sorted list (and every fourth
  differential suite); unset, the tests run everything.
- `cross-link` (linux-x64): `targets/build.sh` for the Linux targets and `i686-pc-windows-msvc`, then the
  sysroot link test.
- `cross`, per target and level: the corpora for `ROK_TEST_TARGET` on a host that runs it:
  `i686-unknown-linux-gnu` (the i386 loader), `armv7-unknown-linux-gnueabihf` (qemu-user) and
  `x86_64-unknown-linux-musl` (static) on linux-x64, `i686-pc-windows-msvc` (WOW64) on windows-x64,
  `aarch64-pc-windows-msvc` on windows-arm64, whose rokc is the x64 build under emulation with the x64
  prefix.
- `wasm` (linux-x64), per wasm32 target: `targets/test-wasm.sh <target>`, with the image's node and clang.
- `bindgen` (linux-x64 and windows-x64, nightly and manual runs only): libclang and clang's resource
  headers (~40 MB, `.github/actions/libclang-prefix`: `llvm/build-libclang.sh`, Windows
  `llvm/build-libclang.ps1`) under their own cache key (`libclang-<os>-<arch>-<hash of the script>`), apart
  from the LLVM prefix, whose key and contents they do not touch; built only when the script changes (on a
  self-hosted runner kept in the default cache directory). Then the `rokc bindgen` tests (`cargo test --test
  cli -- bindgen`) with `ROK_REQUIRE_LIBCLANG=1`. Elsewhere those tests skip with a notice when no libclang
  is built.
- `dist` (windows-x64, nightly and manual runs only): `./dist.sh` (Git Bash with the MSVC environment of
  `llvm-prefix`, the LLVM and libclang prefixes above; `targets/build.sh` falls back to the image's `python`
  / `mingw32-make`), then `install.ps1 -NoModifyPath` into a scratch `ROK_HOME` and, with only
  its `bin\` on PATH, `rok run` of a file and a `rok new --lib --bin` package's build / run / `--release`
  build / test.

## Self-hosted runners

linux-x64 and windows-x64 run on a self-hosted runner when the repository variable `ROK_LINUX_RUNNER` /
`ROK_WINDOWS_RUNNER` is `self-hosted` (Settings → Secrets and variables → Actions → Variables); otherwise on
GitHub's.

- Labels: `self-hosted, linux, x64` / `self-hosted, windows, x64` (the runner's defaults on that OS and
  architecture).
- Service: configure with `./config.sh` (`config.cmd`), then install it as a service: `sudo ./svc.sh install
  && sudo ./svc.sh start` on Linux; on Windows answer yes to "run as service" in `config.cmd`.
- Persistent directory: set `ROK_CI_HOME` in the runner's `.env` file (next to `config.sh`; restart the
  service), e.g. `ROK_CI_HOME=/var/lib/rok-ci` or `ROK_CI_HOME=D:\rok-ci`. It holds the LLVM prefixes
  (`llvm-<version>-<arch>-<hash>`, marked complete by `.complete`; delete old ones by hand) and one cargo
  target directory per runner (`target/<runner name>`), outside the workspace and instead of the actions
  cache. Runners on one machine share the prefixes; give each its own name.
- Prerequisites: Linux: rustup, clang-19, curl, xz, make, python3, cmake and ninja (`llvm/build.sh`), and for
  the cross targets `libc6-i386 libc6-armhf-cross qemu-user-binfmt`, node 18+ for wasm. Windows: rustup,
  Git for Windows (bash), Visual Studio or its Build Tools with `VC.Tools.x86.x64` (the MSVC environment comes from
  `vswhere`), clang (`targets/build.sh`), cmake and ninja (`llvm/build.ps1`), python3 and make for `dist`.
- Security: a self-hosted runner runs whatever a workflow gives it. Pull requests from forks never get one:
  the plan job forces GitHub-hosted runners when `github.event.pull_request.head.repo.full_name !=
  github.repository`, and today no pull request job runs on Windows. On a public repository also keep
  "Require approval for all outside collaborators" (Settings → Actions → General) and put the runners in a
  runner group limited to this repository.

## Nightly schedule

The cron schedule runs only where the repository variable `ROK_NIGHTLY` is `on`, so a private copy pays for nightly runs (macOS included) only when it opts in.
