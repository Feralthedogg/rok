# rok

rok 언어의 구현입니다: 컴파일러 `rokc`, 패키지 / 빌드 front-end `rok`, 언어 서버 `rokls`,
런타임 `librokr.a`, 표준 라이브러리 (`library/{core,std,bare}`). 언어 명세는
[rok-lang/spec](https://github.com/rok-lang/spec), 소개와 시작 안내는 [rok-lang.org](https://rok-lang.org) 에
있습니다.

## 요구 사항

- **LLVM 21 (MLIR 포함)** — `rokc` 는 LLVM 을 링크하지 않고 `mlir-opt` / `mlir-translate` / `clang` 을 프로세스로
  실행합니다. LLVM 21 과 22 를 지원합니다. `rokc` 는 `PATH` 를 먼저, 그다음 `/opt/homebrew/opt/llvm@21/bin`,
  `/usr/local/opt/llvm@21/bin`, `/usr/lib/llvm-21/bin` 등을 찾으므로 보통 `PATH` 를 바꿀 필요가 없습니다.
  - macOS: `brew install llvm@21`
  - Debian / Ubuntu: [apt.llvm.org](https://apt.llvm.org) 의 `mlir-21-tools clang-21`
- macOS 에서 최종 링크는 Xcode (Command Line Tools) 의 clang (`xcrun clang`) 으로 합니다. Homebrew 의 clang 이
  `PATH` 앞에 있어도 SDK 의 `.tbd` 를 못 읽는 일이 없습니다. 다른 링커 드라이버는 `ROK_CC` 로 지정합니다.
- REPL / Jupyter 는 LLVM 의 공유 라이브러리 (`libLLVM`) 와 C API 헤더도 씁니다 (Homebrew 의 LLVM 에 들어 있음).
- 소스에서 빌드하려면 Rust (`rust-toolchain.toml`). 외부 crate 는 쓰지 않습니다.

## 설치

```sh
curl -fsSL https://rok-lang.org/install.sh | sh
```

또는 릴리스 archive 로:

```sh
sh install.sh --archive rok-0.1.0-aarch64-apple-darwin.tar.gz
# 풀어 둔 archive 안에서는
rok-0.1.0-aarch64-apple-darwin/install.sh
```

설치 뒤 `~/.rok/bin` 을 `PATH` 에 더합니다 (스크립트가 안내합니다).

```sh
export PATH="$HOME/.rok/bin:$PATH"      # bash / zsh
fish_add_path ~/.rok/bin                 # fish
```

## 설치 레이아웃

rustup / cargo 식입니다 (spec 9.2.19). `ROK_HOME` 의 기본값은 `~/.rok` 입니다.

```
$ROK_HOME/
├── bin/{rok,rokc,rokls}              proxy: 활성 toolchain 의 같은 이름 실행 파일을 실행
├── toolchains/<version>-<triple>/    자기 완결 toolchain
│   ├── bin/{rok,rokc,rokls}
│   └── lib/librokr.a, lib/rok/{core,std,bare}/
├── cache/                            git, registry, 스크립트 lock
├── envs/<name>/, envs/CURRENT        이름 있는 환경
└── config.rokon                      Config { registry: "..", toolchain: ".." }
```

- `rokc` 는 표준 라이브러리와 런타임을 자기 실행 파일 기준 (sysroot = `bin/..`) 에서 찾고, `ROK_HOME` 은 보지
  않습니다. 저장소에서 빌드한 `rokc` (`target/<profile>/rokc`) 는 저장소의 `library/` 와 옆의 `librokr.a` 를 씁니다.
- 활성 toolchain: `rok +<version> ..` > `ROK_TOOLCHAIN` > 가장 가까운 `rok.rokon` 의 `toolchain: "X"` >
  `rok toolchain default`.

```sh
rok toolchain list
rok toolchain install 0.1.0 --from rok-0.1.0-aarch64-apple-darwin.tar.gz   # 디렉토리, archive, URL
rok toolchain default 0.1
rok toolchain remove 0.1.0-aarch64-apple-darwin
```

## 빠른 시작

```sh
rok new hello        # hello/{main.rok, rok.rokon, .gitignore} + git init
cd hello
rok run              # Hello, world!
rok test
rok jupyter install  # Jupyter / VS Code 의 rok 커널
```

## 소스에서 빌드

```sh
cargo build --release                 # target/release/{rok,rokc,rokls}, librokr.a
./dist.sh                             # dist/rok-<version>-<triple>.tar.gz (+ .sha256)
sh install.sh --archive dist/rok-*.tar.gz
```

개발 중에는 `target/debug/rok` / `rokc` 를 그대로 써도 됩니다 (저장소의 `library/` 를 찾음).

### 검사

```sh
cargo fmt --all --check
cargo clippy --all-targets -- -D warnings
ROK_REQUIRE_LLVM=1 cargo test --no-fail-fast
ROK_TEST_OPT=-O2 ROK_REQUIRE_LLVM=1 cargo test --test integration
cargo run -p rokc -- fmt --check library
```

## 라이선스

`MIT OR Apache-2.0` ([LICENSE-MIT](LICENSE-MIT), [LICENSE-APACHE](LICENSE-APACHE)). 명세 저장소는 CC-BY-4.0 입니다.
