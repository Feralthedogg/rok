# Builds libclang (the DLL) and clang's resource headers from the pinned
# LLVM source on a Windows host (MSVC ABI), for `rokc bindgen`. The
# counterpart of build-libclang.sh.
#
#   powershell -ExecutionPolicy Bypass -File llvm\build-libclang.ps1 [prefix]
#
# prefix defaults to $env:ROK_LLVM_CACHE\libclang-<version>, ROK_LLVM_CACHE
# to %LOCALAPPDATA%\rok. Independent of build.ps1's prefix: rokc loads
# libclang at run time. The source and build trees live beside the
# prefix and are deleted once the install succeeds.
#
# Installs lib\libclang.dll (moved from bin\, so the layout is the Unix
# one) and lib\clang\<major>\include only, with the dynamic CRT (/MD).
# No LLVM back end is built. Needs what build.ps1 needs (cmake, ninja and
# the MSVC C++ build tools on PATH) plus python.
param([string]$Prefix)
$ErrorActionPreference = 'Stop'

$Version = '22.1.8'
$Sha256 = '922f1817a0df7b1489272d18134ee0087a8b068828f87ac63b9861b1a9965888'

$cache = if ($env:ROK_LLVM_CACHE) { $env:ROK_LLVM_CACHE } else { Join-Path $env:LOCALAPPDATA 'rok' }
if (-not $Prefix) { $Prefix = Join-Path $cache "libclang-$Version" }
$work = "$Prefix.work"
$jobs = if ($env:ROK_LLVM_JOBS) { $env:ROK_LLVM_JOBS } else { $env:NUMBER_OF_PROCESSORS }
$major = $Version.Split('.')[0]

$cxx = if ($env:CXX) { $env:CXX } else { 'cl' }
foreach ($tool in 'cmake', 'ninja', $cxx) {
    if (-not (Get-Command $tool -ErrorAction SilentlyContinue)) {
        throw "build-libclang.ps1: $tool is not on PATH (see the top of this script)"
    }
}

if ((Test-Path "$Prefix\lib\libclang.dll") -and (Test-Path "$Prefix\lib\clang\$major\include\stddef.h")) {
    Write-Output "libclang $Version already in $Prefix"
    exit 0
}

New-Item -ItemType Directory -Force $work | Out-Null
# build.ps1's tarball when it is still there.
$tarball = "$work\llvm-project-$Version.src.tar.xz"
foreach ($t in "$cache\llvm-project-$Version.src.tar.xz", "$cache\llvm-$Version.work\llvm-project-$Version.src.tar.xz") {
    if (-not (Test-Path $tarball) -and (Test-Path $t)) { $tarball = $t }
}
if (-not (Test-Path $tarball)) {
    $url = "https://github.com/llvm/llvm-project/releases/download/llvmorg-$Version/llvm-project-$Version.src.tar.xz"
    Invoke-WebRequest -UseBasicParsing -Uri $url -OutFile "$tarball.part"
    Move-Item -Force "$tarball.part" $tarball
}
$got = (Get-FileHash -Algorithm SHA256 $tarball).Hash.ToLower()
if ($got -ne $Sha256) { throw "checksum mismatch for ${tarball}: $got" }

$src = "$work\llvm-project-$Version.src"
if (-not (Test-Path $src)) {
    $top = "llvm-project-$Version.src"
    Push-Location $work
    try {
        cmake -E tar xf $tarball "$top/llvm" "$top/clang" "$top/cmake" "$top/third-party"
        if ($LASTEXITCODE) { throw "cannot unpack $tarball" }
    } finally { Pop-Location }
}

function Run {
    & $args[0] @($args[1..($args.Count - 1)])
    if ($LASTEXITCODE) { throw "$($args -join ' ') failed" }
}

Run cmake -G Ninja -S "$src\llvm" -B "$work\build" `
    -DCMAKE_BUILD_TYPE=Release `
    "-DCMAKE_INSTALL_PREFIX=$Prefix" `
    -DCMAKE_MSVC_RUNTIME_LIBRARY=MultiThreadedDLL `
    -DLLVM_ENABLE_PROJECTS=clang `
    "-DLLVM_TARGETS_TO_BUILD=" `
    -DLLVM_ENABLE_ASSERTIONS=OFF `
    -DLLVM_ENABLE_RTTI=OFF `
    -DLLVM_BUILD_TOOLS=OFF `
    -DLLVM_BUILD_UTILS=OFF `
    -DLLVM_INCLUDE_TESTS=OFF `
    -DLLVM_INCLUDE_BENCHMARKS=OFF `
    -DLLVM_INCLUDE_EXAMPLES=OFF `
    -DLLVM_INCLUDE_DOCS=OFF `
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
    -DCLANG_BUILD_TOOLS=OFF `
    -DCLANG_INCLUDE_TESTS=OFF `
    -DCLANG_INCLUDE_DOCS=OFF `
    -DCLANG_ENABLE_STATIC_ANALYZER=OFF `
    -DCLANG_PLUGIN_SUPPORT=OFF `
    "-DCLANG_PYTHON_BINDINGS_VERSIONS="
Run cmake --build "$work\build" --target libclang -j $jobs
Run cmake --build "$work\build" --target install-libclang-stripped install-clang-resource-headers -j $jobs

# The DLL beside the headers, as on Unix; the import library is not used.
Move-Item -Force "$Prefix\bin\libclang.dll" "$Prefix\lib\libclang.dll"
Remove-Item -Recurse -Force "$Prefix\bin", "$Prefix\lib\libclang.lib", "$Prefix\include" -ErrorAction SilentlyContinue

Remove-Item -Recurse -Force $work
Write-Output "libclang $Version in $Prefix"
