# Builds the pinned LLVM + MLIR + lld that rokc links statically, on a
# Windows host (MSVC ABI). The counterpart of build.sh.
#
#   powershell -ExecutionPolicy Bypass -File llvm\build.ps1 [prefix]
#
# prefix defaults to $env:ROK_LLVM_CACHE\llvm-<version>, ROK_LLVM_CACHE to
# %LOCALAPPDATA%\rok. The source and build trees live beside the prefix
# and are deleted once the install succeeds. Build rokc against the
# result with ROK_LLVM_PREFIX=<prefix> (or leave it at the default).
#
# Release static libraries only, with the dynamic CRT (/MD, what rustc
# links), no DIA SDK, zlib, zstd or libxml2. Needs, on PATH: cmake,
# ninja and the MSVC C++ build tools (run from a "Developer PowerShell
# for VS" / "x64 Native Tools" prompt; ARM64 hosts: the arm64 one).
# CC / CXX pick another compiler (clang-cl). Only building rok needs
# these: the toolchain it makes needs no MSVC or Windows SDK.
#
# PGO: build.sh's rok.profdata.xz names functions by their Itanium
# mangling, which an MSVC-ABI build does not have; rok-msvc.profdata.tar.xz
# (made by train-pgo.ps1) is the profile for it. clang-cl uses it when it
# can read it; cl reads no clang profile. ROK_LLVM_INSTRUMENT=1 builds the
# instrumented libraries train-pgo.ps1 profiles instead (clang-cl).
param([string]$Prefix)
$ErrorActionPreference = 'Stop'

$Version = '22.1.8'
$Sha256 = '922f1817a0df7b1489272d18134ee0087a8b068828f87ac63b9861b1a9965888'
$Targets = 'AArch64;X86;ARM;RISCV;WebAssembly'

$cache = if ($env:ROK_LLVM_CACHE) { $env:ROK_LLVM_CACHE } else { Join-Path $env:LOCALAPPDATA 'rok' }
if (-not $Prefix) { $Prefix = Join-Path $cache "llvm-$Version" }
$work = "$Prefix.work"
$jobs = if ($env:ROK_LLVM_JOBS) { $env:ROK_LLVM_JOBS } else { $env:NUMBER_OF_PROCESSORS }

$cxx = if ($env:CXX) { $env:CXX } else { 'cl' }
foreach ($tool in 'cmake', 'ninja', $cxx) {
    if (-not (Get-Command $tool -ErrorAction SilentlyContinue)) {
        throw "build.ps1: $tool is not on PATH (see the top of this script)"
    }
}

function Built {
    (Test-Path "$Prefix\lib\cmake\mlir\MLIRConfig.cmake") -and (Test-Path "$Prefix\lib\lldCommon.lib")
}
$dsym = "$Prefix\share\rok\dsymutil"
if ((Built) -and (Test-Path "$dsym\Options.inc")) {
    Write-Output "LLVM $Version already in $Prefix"
    exit 0
}

New-Item -ItemType Directory -Force $work | Out-Null
$tarball = "$work\llvm-project-$Version.src.tar.xz"
if (-not (Test-Path $tarball)) {
    $url = "https://github.com/llvm/llvm-project/releases/download/llvmorg-$Version/llvm-project-$Version.src.tar.xz"
    Invoke-WebRequest -UseBasicParsing -Uri $url -OutFile "$tarball.part"
    Move-Item -Force "$tarball.part" $tarball
}
$got = (Get-FileHash -Algorithm SHA256 $tarball).Hash.ToLower()
if ($got -ne $Sha256) { throw "checksum mismatch for ${tarball}: $got" }

$src = "$work\llvm-project-$Version.src"
if (-not (Test-Path $src)) {
    # Only what the build reads; cmake's tar reads xz.
    $top = "llvm-project-$Version.src"
    Push-Location $work
    try {
        cmake -E tar xf $tarball "$top/llvm" "$top/mlir" "$top/lld" "$top/cmake" `
            "$top/third-party" "$top/libunwind/include"
        if ($LASTEXITCODE) { throw "cannot unpack $tarball" }
    } finally { Pop-Location }
}

function Run {
    & $args[0] @($args[1..($args.Count - 1)])
    if ($LASTEXITCODE) { throw "$($args -join ' ') failed" }
}

$extra = @()
$pgo = Join-Path $PSScriptRoot 'rok-msvc.profdata.tar.xz'
if ($env:ROK_LLVM_INSTRUMENT) {
    $extra = @('-DLLVM_BUILD_INSTRUMENTED=IR')
} elseif (Test-Path $pgo) {
    Push-Location $work
    try { Run cmake -E tar xf $pgo } finally { Pop-Location }
    $data = "$work\rok-msvc.profdata"
    # clang-cl reads the profile even for an empty unit. (Its errors on
    # stderr must not stop the script.)
    Set-Content -Path "$work\probe.cpp" -Value 'int x;'
    $ErrorActionPreference = 'Continue'
    & $cxx /nologo /c "/Fo$work\probe.obj" "-fprofile-instr-use=$data" "$work\probe.cpp" 2>$null | Out-Null
    $failed = $LASTEXITCODE
    $ErrorActionPreference = 'Stop'
    if ($failed) {
        Write-Warning "$cxx cannot read $pgo (cl, or a clang-cl older than its format): building LLVM without PGO"
    } else {
        $extra = @("-DLLVM_PROFDATA_FILE=$data")
    }
}

Run cmake -G Ninja -S "$src\llvm" -B "$work\build" `
    -DCMAKE_BUILD_TYPE=Release `
    "-DCMAKE_INSTALL_PREFIX=$Prefix" `
    -DCMAKE_MSVC_RUNTIME_LIBRARY=MultiThreadedDLL `
    "-DLLVM_ENABLE_PROJECTS=mlir;lld" `
    "-DLLVM_TARGETS_TO_BUILD=$Targets" `
    -DLLVM_ENABLE_ASSERTIONS=OFF `
    -DLLVM_ENABLE_RTTI=OFF `
    -DLLVM_BUILD_TOOLS=OFF `
    -DLLVM_BUILD_UTILS=OFF `
    -DLLVM_INCLUDE_TESTS=OFF `
    -DLLVM_INCLUDE_BENCHMARKS=OFF `
    -DLLVM_INCLUDE_EXAMPLES=OFF `
    -DLLVM_INCLUDE_DOCS=OFF `
    -DMLIR_INCLUDE_TESTS=OFF `
    -DMLIR_ENABLE_BINDINGS_PYTHON=OFF `
    -DLLVM_ENABLE_BINDINGS=OFF `
    -DLLVM_ENABLE_DIA_SDK=OFF `
    -DLLVM_ENABLE_ZLIB=OFF `
    -DLLVM_ENABLE_ZSTD=OFF `
    -DLLVM_ENABLE_LIBXML2=OFF `
    -DLLVM_ENABLE_LIBEDIT=OFF `
    -DLLVM_ENABLE_LIBPFM=OFF `
    -DLLVM_ENABLE_TERMINFO=OFF `
    -DLLVM_ENABLE_Z3_SOLVER=OFF `
    -DLLVM_ENABLE_CURL=OFF `
    -DLLVM_ENABLE_HTTPLIB=OFF `
    @extra
if (-not (Built)) {
    Run cmake --build "$work\build" --target install -j $jobs
}

# dsymutil is a tool, not a library: rokc compiles its sources itself
# (rokc_llvm's build.rs), with the option table generated here.
Run cmake --build "$work\build" --target DsymutilTableGen -j $jobs
New-Item -ItemType Directory -Force "$dsym\llvm\Config" | Out-Null
Copy-Item "$src\llvm\tools\dsymutil\*.cpp", "$src\llvm\tools\dsymutil\*.h" $dsym
# A private header of the build tree the sources include.
Copy-Item "$work\build\include\llvm\Config\config.h" "$dsym\llvm\Config\"
Copy-Item "$work\build\tools\dsymutil\Options.inc" $dsym

Remove-Item -Recurse -Force $work
Write-Output "LLVM $Version in $Prefix"
