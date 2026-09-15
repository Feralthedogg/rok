# Regenerates llvm/rok-msvc.profdata.tar.xz, the profile build.ps1
# optimizes an MSVC-ABI LLVM with (build.sh's rok.profdata.xz names
# functions by their Itanium mangling). The counterpart of train-pgo.sh.
#
#   powershell -ExecutionPolicy Bypass -File llvm\train-pgo.ps1 [workdir]
#
# Builds an instrumented LLVM with clang-cl (build.ps1 with
# ROK_LLVM_INSTRUMENT=1) and a release rokc against it, then has that
# rokc build three quarters of compiler\rokc\tests\cases at -O2: two of
# three for the host (linked), the third as objects for the other Windows
# architecture, so both main back ends are warm. The rest of the cases
# and bench\ are left to measure the result. Needs what build.ps1 does,
# with clang-cl and llvm-profdata of one LLVM installation on PATH;
# workdir (default $env:ROK_LLVM_CACHE\pgo) needs ~25 GB and is deleted
# afterwards. Build with the profile: CXX=clang-cl, build.ps1.
param([string]$Work)
$ErrorActionPreference = 'Stop'

$root = Split-Path -Parent $PSScriptRoot
$cache = if ($env:ROK_LLVM_CACHE) { $env:ROK_LLVM_CACHE } else { Join-Path $env:LOCALAPPDATA 'rok' }
if (-not $Work) { $Work = Join-Path $cache 'pgo' }
$prof = "$Work\profiles"
foreach ($tool in 'clang-cl', 'llvm-profdata', 'cargo') {
    if (-not (Get-Command $tool -ErrorAction SilentlyContinue)) {
        throw "train-pgo.ps1: $tool is not on PATH (see the top of this script)"
    }
}

function Run {
    & $args[0] @($args[1..($args.Count - 1)])
    if ($LASTEXITCODE) { throw "$($args -join ' ') failed" }
}

$env:CC = 'clang-cl'
$env:CXX = 'clang-cl'
$env:ROK_LLVM_INSTRUMENT = '1'
Run powershell -NoProfile -ExecutionPolicy Bypass -File "$PSScriptRoot\build.ps1" "$Work\llvm"
Remove-Item Env:ROK_LLVM_INSTRUMENT, Env:CC

# The instrumented archives name clang_rt.profile.lib (/DEFAULTLIB),
# which the link finds in clang's runtime directory. The shim is
# compiled by clang-cl too (CXX); the REPL host by clang (CC unset).
$rt = Split-Path -Parent (& clang-cl /clang:-print-libgcc-file-name /clang:--rtlib=compiler-rt)
$env:ROK_LLVM_PREFIX = "$Work\llvm"
$env:CARGO_TARGET_DIR = "$Work\target"
$env:RUSTFLAGS = "-Clink-arg=/LIBPATH:$rt"
Push-Location $root
try { Run cargo build --release -q -p rokc -p rokr } finally { Pop-Location }
Remove-Item Env:RUSTFLAGS, Env:CXX
$rokc = "$Work\target\release\rokc.exe"
$rokr = "$Work\target\release\rokr.lib"

if (Test-Path $prof) { Remove-Item -Recurse -Force $prof }
New-Item -ItemType Directory -Force "$prof\out", "$prof\log" | Out-Null
$env:LLVM_PROFILE_FILE = "$prof\%m.profraw"
$env:ROK_HOME = $root
$other = if ($env:PROCESSOR_ARCHITECTURE -eq 'ARM64') { 'x86_64-pc-windows-msvc' } else { 'aarch64-pc-windows-msvc' }
$jobs = [int]$env:NUMBER_OF_PROCESSORS
$i = 0
$n = 0
$running = @()
foreach ($f in Get-ChildItem "$root\compiler\rokc\tests\cases\*.rok") {
    if (Select-String -Quiet -SimpleMatch -Pattern 'expect-error', 'rokc-arg' -Path $f.FullName) { continue }
    $i++
    if ($i % 4 -eq 0) { continue }
    $n++
    $a = if ($n % 3 -eq 0) {
        '-q', 'build', $f.FullName, '-O2', "--target=$other", '--emit=obj', '-o', "$prof\out\$n.obj"
    } else {
        '-q', 'build', $f.FullName, '-O2', '--rokr', $rokr, '-o', "$prof\out\$n.exe"
    }
    # Start-Process joins its arguments with spaces: quote each.
    $running += Start-Process -FilePath $rokc -ArgumentList ($a | ForEach-Object { "`"$_`"" }) `
        -NoNewWindow -PassThru -RedirectStandardOutput "$prof\log\$n.out" -RedirectStandardError "$prof\log\$n.err"
    if ($running.Count -ge $jobs) {
        $running | Wait-Process
        $running = @()
    }
}
if ($running) { $running | Wait-Process }

# Sparse: functions the corpus never ran get no profile (optimized as
# without PGO) rather than a cold one.
Run llvm-profdata merge --sparse -o "$Work\rok-msvc.profdata" (Get-ChildItem "$prof\*.profraw").FullName
Push-Location $Work
try { Run cmake -E tar cJf "$PSScriptRoot\rok-msvc.profdata.tar.xz" rok-msvc.profdata } finally { Pop-Location }
Remove-Item -Recurse -Force $Work
Get-Item "$PSScriptRoot\rok-msvc.profdata.tar.xz"
