# Drift 감사 — spec ↔ impl 양방향

직전 감사가 놓친 차원: "spec엔 있는데 impl엔 없는" 만 봤지, "impl엔 있는데 spec엔 없는"
드리프트는 보지 않았다. 또 "있긴 있는데 시그니처/값이 다른" mismatch도 추정만 했다.
이 문서는 6개 영역에서 양쪽 표를 1:1로 대조한 결과.

기준 시점: 2026-04-29 (302 등급 정렬 + broadcast 트레잇 등록 후)
방법: spec 표(BNF / 표 / 코드 블록)에서 항목을 추출하고, 구현 측 등록 표
(`TokenKind`, ops.rok `#[infix]`, `pub extern "C"`, clap `Args`)와 set diff.

---

## 1. 105 키워드 ↔ `keyword_kind()` (`rokc_lexer/src/token.rs:204`)

**완전 정렬.** spec 105.1의 6개 분류 모두 impl 측에 1:1 매핑.

차이 없음.

---

## 2. 110 고정 토큰 ↔ `TokenKind` (`rokc_lexer/src/token.rs:107-187`)

**완전 정렬.** spec 110.3의 모든 고정 토큰이 impl `TokenKind`에 존재:

- 산술/비교/논리: ✓ (Plus, Minus, Star, Slash, Percent, EqEq, NotEq, Lt, Gt, LtEq, GtEq, AmpAmp, PipePipe, Bang, Amp, Pipe, Caret, Tilde, Shl, Shr)
- 브로드캐스트 16개: ✓ (DotPlus..DotShr 모두 등록)
- 대입 11개: ✓
- 범위/슬라이스: ✓ (DotDot, DotDotEq, Colon, ColonColon)
- 점/물음표: ✓ (Dot, QuestionDot, QuestionQuestion, Question)
- 람다/화살표: ✓
- 구두점: ✓
- 속성 도입자: ✓ (HashLBracket, HashBangLBracket)

확장 메커니즘: spec 110.4 ↔ `TokenKind::UserOp(String)` ✓.

차이 없음.

---

## 3. 805 extern symbols ↔ `runtime/rokr/src/lib.rs`

### 3.1. spec → impl: spec에 정의됐는데 impl 누락

| Spec 8.5.x | 심볼 | 구현 상태 |
|---|---|---|
| 8.5.1 | `rok_gc_pin(obj) -> Ptr<u8>` | ✓ stub 추가 (2026-04-28) — pin/unpin은 stage-1엔 identity |
| 8.5.1 | `rok_gc_unpin(obj)` | ✓ stub 추가 |
| 8.5.1 | `rok_gc_collect()` | ✓ stub 추가 — no-op |
| 8.5.2 | `rok_thread_init()` | ✓ stub 추가 — no-op |
| 8.5.2 | `rok_thread_shutdown()` | ✓ stub 추가 — no-op |
| 8.5.6 | `rok_throw(exc) -> !` | ✓ stub 추가 — abort (longjmp 미구현) |
| 8.5.6 | `rok_exception_current() -> Ptr<u8>` | ✓ stub 추가 — null 반환 |

**3.1 → 0개 누락 (모두 spec 시그니처대로 stub 추가됨, 2026-04-28)**

### 3.2. spec ↔ impl: 시그니처 mismatch

| 심볼 | Spec 시그니처 | Impl 시그니처 | 비고 |
|---|---|---|---|
| `rok_panic` | `(msg: ConstPtr<u8>, msg_len: usize) -> !` (8.5.7) | `(code: i32) -> !` (`lib.rs:304`) | **mismatch** — spec은 메시지+길이, impl은 코드 정수 |
| `rok_par_for` | `(start, end, step: i64, callback: Ptr<u8>)` (8.5.4) | `(start, end, step: i64, callback: extern "C" fn(i64))` (`lib.rs:163`) | 콜백 타입 — spec: 불투명 포인터, impl: 타입 있는 함수 포인터 |
| `rok_par_scope` | `(callback: Ptr<u8>)` | `(callback: extern "C" fn(*mut u8))` (`lib.rs:172`) | 동일 — 타입 있는 함수 포인터 |
| `rok_timer_register` | `deadline: u64` (단위 구현 결정) (8.5.5) | `_deadline_ns: u64` (`lib.rs:159`) | impl이 ns로 명시 — spec 허용범위 안이지만 문서화 필요 |

### 3.3. impl → spec: spec 없는데 impl이 노출 (drift)

| 심볼 | Impl 위치 | 분류 |
|---|---|---|
| `rust_eh_personality` | `lib.rs:31` | Rust 내부 — spec 대상 아님 (OK) |
| `rok_alloc(size, align) -> *mut u8` | `lib.rs:64` | **drift** — `rok_gc_alloc_slow`의 사용자용 wrapper, spec 없음 |
| `rok_free(ptr)` | `lib.rs:69` | **drift** — spec에 없음 (GC 모델에선 free 없음) |
| `rok_load_i32 / rok_load_i64 / rok_load_f64` | `lib.rs:80,90,100` | **drift** — 타입드 메모리 접근, spec 없음 |
| `rok_store_i32 / rok_store_i64 / rok_store_f64` | `lib.rs:85,95,105` | **drift** |
| `rok_print_i64 / rok_print_i32 / rok_print_str / rok_print_f64 / rok_print_bool` | `lib.rs:189-220` | **drift** — 진단 출력, spec엔 rok_panic만 8.5.7에 정의 |
| `rok_write_str / rok_write_i64 / rok_write_f64 / rok_write_hex` | `lib.rs:239-262` | **drift** |
| `rok_str_len / rok_str_eq` | `lib.rs:277,288` | **drift** |
| `rok_assert(cond) -> i32` | `lib.rs:313` | **drift** |

요약: spec 805는 27개 심볼 정의, impl은 39개 심볼 노출.
**spec 누락 7개**, **시그니처 mismatch 4개**, **drift 19개**(rust_eh_personality 제외 18개).

`rok_print_*` / `rok_write_*` / `rok_str_*` / `rok_alloc` / `rok_load/store_*` 가 stage-1
편의용으로 추가됐는데 spec 805에 등록 절차가 없다 — spec에 정식 등재하든지, 별도
"stage-1 임시 심볼" 부록으로 빼야 함.

---

## 4. 302 우선순위 ↔ `library/core/ops.rok`

### 4.1. 우선순위 등급 비교 (2026-04-29 갱신)

spec 302.3 이 **사용자 의도 정렬 회차에서 갱신** — ops.rok 의 실제 등록값을
권위로 명시하고 spec 표를 거기에 맞춤. 두 자리가 이제 일치한다.

| 토큰류 | Spec 302.3 | ops.rok | 같음? |
|---|---|---|---|
| `*` `/` `%` | 8 | 8 | ✓ |
| `+` `-` (이항) | 7 | 7 | ✓ |
| `<<` `>>` | 9 | 9 | ✓ |
| `&` `^` | 6 | 6 | ✓ |
| `|` | 5 | 5 | ✓ |
| `==` `!=` `<` `>` `<=` `>=` | 4 | 4 | ✓ |
| `&&` | 3 | 3 | ✓ |
| `||` | 2 | 2 | ✓ |
| 전위 `-` `!` `~` | 11 | 11 | ✓ |

이전 회차의 "산술 > 시프트 vs 시프트 > 산술" 충돌은 spec 갱신으로 해결.

### 4.2. broadcast 트레잇 등록 (2026-04-28 회차에 닫힘)

spec 110.3 의 16개 broadcast 토큰 (`.+ .- .* ./ .% .== .!= .< .> .<= .>= .& .| .^ .<< .>>`)
모두 `core/ops.rok` 에 트레잇으로 등록 완료. 직전 감사의 "12개 미등록" 항목
모두 닫힘:

| 트레잇 | 등록 위치 (`ops.rok`) |
|---|---|
| `DotRem` | line 164 |
| `DotCmp` (Eq/Ne/Lt/Gt/Le/Ge 6종) | line 170+ |
| `DotBitAnd`/`DotBitOr`/`DotBitXor` | line 190/196/202 |
| `DotShl`/`DotShr` | line 208/214 |

### 4.3. 비결합(none) 일관성

spec 302.5: 비교 6개 모두 비결합 → impl 모두 `none`. ✓

### 4.4. cmp 체이닝 거부 (2026-04-28 회차에 닫힘)

`a < b < c` 같은 비결합 연산자 체이닝이 spec 302.5 에선 명시 거부지만
`parse_expr_bp` 가 chain 통과시켰던 갭. 같은 prec 의 비결합 연산자가 두 번
연속하면 에러 emit 하도록 수정 (`last_none_prec` 추적). probe `302_5_cmp_chain`
가 이를 검증.

### 4.5. 조합 부재

spec 304 가 정의하는 `=`, `+=` ... 11개 대입 연산자는 ops.rok 에 등록 없음.
대입은 트레잇 dispatch 가 아닌 언어 내장으로 처리 — spec 304 에서 desugar
규칙 명시. impl `parser.rs` 에서 직접 처리.

---

## 5. 901 CLI ↔ `rokc/src/main.rs`

### 5.1. 서브명령 (spec 9.1.1 BNF)

```
subcommand ::= "build" | "run" | "test" | "repl" | "jupyter" | "fmt"
             | "check" | "lsp" | "demangle" | "rhir-text" | "inspect"
             | "new" | "clean" | "version" | "help"
```

| 서브명령 | 구현 |
|---|---|
| `build` | ✓ `Cmd::Build` (`main.rs:30`) |
| `run` | ✓ `Cmd::Run` (`main.rs:32`) |
| `test` | **누락** |
| `repl` | **누락** |
| `jupyter` | **누락** |
| `fmt` | **누락** |
| `check` | **누락** |
| `lsp` | **누락** |
| `demangle` | **누락** |
| `rhir-text` | **누락** |
| `inspect` | **누락** |
| `new` | **누락** |
| `clean` | **누락** |
| `version` | **누락** (clap 기본 `--version`은 있을 수 있지만 서브명령 형태 아님) |
| `help` | **부분** (clap 기본 `--help`만, 서브명령 형태 아님) |

**구현 3/15 (20%)**, drift `emit` 1개.

### 5.2. `emit` 서브명령 (impl 측 drift)

`Cmd::Emit` (`main.rs:28`)은 spec 901에 없는 서브명령.
spec 901.2의 `rokc build --emit=<kind>` 옵션과 기능 중복.
impl이 `rokc emit --stage=hir` 형태로 별도 서브명령화 — **drift**.

### 5.3. `rokc build` 옵션 (spec 9.1.2)

| Spec 옵션 | Impl |
|---|---|
| `--release` | **누락** |
| `-O0`/`-O1`/`-O2`/`-O3`/`-Os` | **누락** |
| `--target=<triple>` | ✓ (`--target`, `BuildArgs.common.target`) |
| `--out=<path>` | mismatch — impl은 `-o`/`--output` (spec은 `--out`) |
| `--cfg <key>=<value>` | ✓ (`--cfg`) |
| `--emit=<kind>` (build에 부속) | **누락** — emit은 별도 서브명령으로만 |

추가 impl-only 옵션 (spec 없음):
- `-L`/`--lib` (라이브러리 검색 경로 + glob `::*`/`::**`) — **drift**
- `--bootstrap` (operator decl 사전 로드 파일) — **drift** (테스트 인프라용)
- `--rokr` (런타임 라이브러리 지정) — **drift** (stage-1 빌드 인프라용)

### 5.4. `--emit=<kind>` 종류 (spec)

spec: `hir mir mlir llvmir asm obj expanded` (7종).
impl: `hir mir mlir` (3종, `cmd_emit` `match args.stage`).
**누락 4종**: `llvmir asm obj expanded`.

---

## 6. AST Item ↔ spec top-level 항목

| spec 정의 | AST `Item::*` | 비고 |
|---|---|---|
| `fn` | `Fn(FnDef)` | ✓ |
| `struct` | `Struct(StructDef)` | ✓ |
| `enum` | `Enum(EnumDef)` | ✓ |
| `union` | `Union(UnionDef)` | ✓ |
| `trait` | `Trait(TraitDef)` | ✓ |
| `impl` | `Impl(ImplDef)` | ✓ |
| `const` | `Const(ConstDef)` | ✓ |
| `static` | `Static(StaticDef)` | ✓ |
| `type` (alias) | `TypeAlias(TypeAliasDef)` | ✓ |
| `mod` | `Mod(ModDef)` | ✓ |
| `use` | `Use(UseDef)` | ✓ |
| `extern` 블록 | `Extern(ExternBlock)` | ✓ |

**완전 정렬.** AST top-level은 spec과 1:1.

---

## 종합 (2026-04-29 갱신)

| 영역 | spec→impl 누락 | 시그니처 mismatch | impl→spec drift | 정렬도 |
|---|---|---|---|---|
| 105 keywords | 0 | 0 | 0 | 100% |
| 110 fixed tokens | 0 | 0 | 0 | 100% |
| 805 extern symbols | 0 (전부 stub 추가) | 4 | 18 (§8.5.12 부록으로 분리) | ~85% |
| 302 precedence | 0 (broadcast 등록 + 등급 spec 갱신) | 0 | 0 | 100% |
| 901 CLI 서브명령 | 12 | 1 (`--out` vs `-o`) | 4 (`emit`, `-L`, `--bootstrap`, `--rokr`) | 20% |
| 901 `--emit` 종류 | 4 | 0 | 0 | 43% |
| AST Items | 0 | 0 | 0 | 100% |

**가장 큰 누락 영역**: 901 (CLI — 12/15 서브명령 미구현, REPL/jupyter/lsp/test/fmt 등).
**남은 drift**: 805 시그니처 mismatch 4건 (`rok_panic` 등 — spec 갱신 또는
impl 시그니처 정렬 결정 필요), `rok_print_*`/`rok_write_*`/`rok_str_*` 등
stage-1 편의 심볼 18개는 spec §8.5.12 "stage-1 진단 심볼" 부록으로 분리됨
(직전 회차 사용자 의도 정렬 #5).
