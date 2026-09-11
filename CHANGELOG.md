# Changelog

## 0.1.0 (unreleased)

첫 릴리스.

- 컴파일러 `rokc` (MLIR / LLVM 21 경유 AOT, REPL, Jupyter 커널, 언어 서버, `fmt`, `lint`, `doc`, `test`, `bench`),
  패키지 / 빌드 front-end `rok` (`rok.rokon` / `rok.lock`, path / git 의존, stone, 환경, toolchain), 런타임
  `librokr.a`, 표준 라이브러리 `core` / `std` / `bare`.
- 설치: rustup 식 레이아웃 (`~/.rok/bin` proxy, `~/.rok/toolchains/<version>-<triple>/`), `install.sh`,
  `dist.sh` 로 만든 `rok-<version>-<triple>.tar.gz`.
- `rok` / `rokc` / `rokls --version` 은 버전, 커밋, 날짜를 출력합니다.
- 라이선스 `MIT OR Apache-2.0`.
