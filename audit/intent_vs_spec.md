> **STALE — superseded by [AUDIT_2026-10-12.md](AUDIT_2026-10-12.md).** 숫자·줄 번호·경로(현재 `library/{bare,core,std}`, 삭제된 `run_probes.sh`)는 당시 기준이며 현재와 다름. 역사 기록으로만 보존.

# i-want-this.txt vs spec/impl — 차이점 전수조사

`i-want-this.txt` (사용자 의도) 1776줄 전체를 spec/ + impl/ 과 대조. 스펙·구현 양쪽이 사용자 의도와 맞는지, 어떻게 다른지 정리.

세 갈래로 분류:

- **drift**: i-want-this.txt 에 없는데 spec/impl 이 추가/명시한 것
- **gap-spec**: i-want-this.txt 에 있는데 spec 이 빠뜨린/잘못 정의한 것
- **gap-impl**: i-want-this.txt 와 spec 둘 다에 있는데 impl 이 미구현/잘못 구현한 것

기준 시점: 2026-04-30 (spec 607 prec 표 정정 후).

---

## 1. 디렉토리 번호 체계 — drift

i-want-this.txt 라인 3-19:
```
000-099: 메타
100-199: 어휘 / 구문
200-299: 타입 시스템
...
하위는 상위 번호 폴더 만들고 그 안에 다시 000부터 시작.
예시: 003/000-*.md  (003 폴더 안의 000 번째 서브 파일)
```
**의도**: 100단위 블록 예약, 3자리 prefix, 하위는 `003/000-*`.

**spec 실제**: `000-meta/`, `001-lexical/`, `002-types/`, `003-expressions/` … 1단위 디렉토리 + 명칭 suffix. 그 안에 `301-…`, `302-…` 처럼 3자리 prefix를 새로 시작.

→ 지시한 100단위 블록 예약 무시. 디렉토리 명명도 다름. **사용자 의도와 spec 디렉토리 구조가 어긋남**.

---

## 2. char 타입 정체성 — spec/impl mismatch

i-want-this.txt 라인 750-751:
```
char literal: 'A' (std 모듈 char)
c_char literal: c'A' (primitive)
```
**의도**: `char`은 stdlib 타입, `c_char` 만 primitive.

**spec 207-niche-optimization.md** (라인 39-48):
```
- 정수형 — i8, i16, i32, i64, u8, u16, u32, u64, usize, isize
- 부동소수형 — f32, f64
...
- char  surrogate 범위 (0xD800..=0xDFFF) — 자동 niche
```
**spec 211-const-generics.md** (라인 43): `- 문자형 (char, c_char).` — char를 c_char와 동급의 const-generic 가능 타입으로 분류.

→ spec이 `char`를 primitive 처럼 다룸. 사용자 의도와 어긋남.

**impl**: `rokc_hir/src/ty.rs:54-68` — primitive 표에 `c_char`만 등록, `char` 없음. **impl은 사용자 의도와 일치**.

→ 이 차이는 spec 207/211을 갱신하거나, char를 정식으로 stdlib에 두고 spec 207의 "char surrogate niche"는 제거 필요.

---

## 3. 가시성 키워드 명명 — drift

i-want-this.txt 라인 211-215:
```
pub(rokrok) -> pub(pkg)
pub(suprok) -> pub(sub)
pub(shyrok) -> pub(shy)
이름만 바뀌고. 역할 그대로
```
**의도**: 4단계 — `pub`, `pub(pkg)`, `pub(sub)`, `pub(shy)`.

**spec 506-visibility.md**: `pub`, `pub(pkg)`, `pub(sub)` 3단계만. `pub(shy)` 없음.

→ **spec 누락**: glob-only 차단 gate `pub(shy)` (i-want-this.txt 라인 1196-1199 명시) 가 spec에 정의 안 됨.

**impl**: parser.rs:1068-1069 `Visibility::Pkg / Sub` 만. `pub(shy)` 미구현.

---

## 4. let 선언 / 재할당 의미론 — gap-impl 가능성

i-want-this.txt 라인 219-258:
```
# 새 선언은 let 으로
let counter = 0i32;
counter = counter + 1i32;   # OK (재할당)
coutner = counter + 1i32;   # ERROR: 'coutner' not declared.
let x = 1;
let x: i32 = 5i32;          # ERROR: redeclaration
```
**의도**: `let` 없이 재할당, `let` 으로만 새 선언, redeclaration 거부 (typo 방지).

**impl**: 검증 필요. 현재 redeclaration 검출이 작동하나 확인되지 않음. 이전 audit 회차에선 별도 probe 없었음.

(probe 작성하면 silent 위반 발견 가능성)

---

## 5. f-string format spec — gap-spec/gap-impl

i-want-this.txt 라인 728-749 — 매우 상세:
```
f"{expr[:spec]}"
spec = [fill][align][sign][#][0][width][.precision][type]
type 별 trait dispatch:
  Display, Debug, DisplayInt, DisplayFloat, LowerHex/UpperHex, LowerExp/UpperExp, Binary, Octal, GeneralFloat
동적 spec: f"{x:.${prec}f}", f"{x:>${width}.${prec}f}"
리터럴 $: f"cost: $100"
```

**spec 107-string-literals.md**: f-string 형식 정의 있으나 type 별 trait dispatch 매핑은 명시 안 됨 (간략).

**impl**: f-string 파스 안 됨 (`Literal::FStr` → `ConstVal::Unit` 직결).

→ f-string 의 dispatch 매핑 (`d` → DisplayInt, `f` → DisplayFloat 등) 이 spec 에 적시 안 됨. **gap-spec**.

---

## 6. 805 extern "C" 심볼 — drift

i-want-this.txt 라인 1681-1709 — 정의된 심볼 21개:
- GC: `rok_gc_alloc_slow`, `rok_gc_wb_slow`, `rok_gc_register_type`
- Safepoint: `rok_runtime_yield`
- Coroutine: `rok_coro_frame_alloc`, `rok_coro_park`, `rok_coro_unpark`
- Scheduler: `rok_task_spawn`, `rok_task_await`, `rok_task_cancel`, `rok_thread_spawn`, `rok_thread_join`, `rok_io_register`, `rok_timer_register`
- Parallel: `rok_par_for`, `rok_par_scope`

**spec 805** 추가 정의 (i-want-this.txt 에 없음):
- `rok_gc_pin`, `rok_gc_unpin` (FFI pinning)
- `rok_gc_collect` (명시 GC 트리거)
- `rok_thread_init`, `rok_thread_shutdown` (worker lifecycle)
- `rok_throw`, `rok_exception_current` (예외 영역 — i-want-this.txt 에 명시되지 않은 unwind 메커니즘)
- `rok_panic(msg, msg_len)` (i-want-this.txt 에 panic 심볼 자체 명시 안 됨)

**impl**: 직전 audit 회차에 spec 805 따라 7개 stub 추가. 추가로 i-want-this.txt 에도 spec에도 없는 ~12개 편의 심볼 (`rok_print_*`, `rok_alloc`, `rok_load_*` 등) 노출 — **stage-1 drift**.

→ spec이 i-want-this.txt 보다 풍부함. impl이 spec 따라감.

---

## 7. 운영자 우선순위 ladder — gap-spec/impl 일치

i-want-this.txt 라인 1148:
```
trait Add { #[infix("+", prec = 7, left)] }
```
즉 `+` prec=7.

**impl** (`library/core/ops.rok`): `+` prec=7, `<<` prec=9 (i-want-this.txt와 일치).

**spec 302.3 예시 ladder**: `+` prec=9, `<<` prec=8 (반대). 결과 `1+2<<3`이 spec 예시는 24, impl/i-want-this.txt는 17.

→ **spec 302.3의 예시 ladder가 i-want-this.txt 의도와 다름**. 사용자 의도(impl) 가 권위라면 spec 갱신 필요.

---

## 8. 사용자 정의 메타 블록 / 템플릿 토큰 — drift

i-want-this.txt 라인 590-641 — 풍부한 사용자 메타:
- `#[impl_derive(TraitName)]`
- `#[impl_attribute(name)]`
- `#[impl_derive_attribute(Trait, attr)]`
- 메타 토큰: `@Self`, `@if_struct`, `@if_enum`, `@if_union`, `@for_fields`, `@field`, `@field.name/type/is_pub/has_attr`, `@for_variants`, `@variant.*`, `@for_variant_fields`, `@apply_if`, `@accept`, `@where_all`, `@where_for_fields`, `@has_derive_attr`, `@derive_attr`, `@item`, `@item.body`, `@attribute`

**spec 608-meta-blocks / 609-template-tokens**: 정의됨 (사용자 의도 반영).

**impl**: 메타 시스템 자체 골격은 직전 회차에 추가됐지만 (`#[lang]` 인식), 메타 블록/템플릿 토큰 전체 미구현.

→ 매우 큰 미구현. 사용자 의도와 spec 정렬, impl 갭 큼.

---

## 9. const fn — gap-impl 가능성

i-want-this.txt 라인 663-708: `const fn` 추가. compile-time 가능한 pure 함수. type 파라미터 금지, 제어흐름 OK, generic 허용 (specialize 후 monomorphic 바디에 CTE).

**spec 502-const.md**: 검증 필요.

**impl**: const fn 미구현 추정.

---

## 10. 점진 함수 (gradual fn) — 명시화 필요

i-want-this.txt 라인 342-364:
```
fn compute(x, y) { return x + y; }
# 내부 변환: fn compute<T, U>(x: T, y: U) -> <T as Add<U>>::Output where T: Add<U>
# 각 호출의 concrete type tuple 마다 specialization
```
**의도**: untyped 파라미터 = implicit generic.

**spec**: 어디에서 정의됐는지 미확인.

**impl**: monomorphize 작동 (직전 회차에 default 적용까지). 단, untyped 파라미터를 가진 fn 자체가 지원되는지 정확히 검증 안 됨.

---

## 11. literal type 변환 매트릭스 — gap-impl

i-want-this.txt 라인 798-806:
```
auto-From (context)        saturate
.into()                     saturate
as i32                      wrap
.try_into::<i32>()          Result<i32,E>
.wrapping_*()               wrap
.saturating_*()             saturate
.checked_*()                Option<T>
```
**의도**: bare literal → stdlib Int → context 타입으로 auto-From + saturate. 명시 변환 메서드 매트릭스.

**spec 214-cast-and-conversion.md**: 매트릭스 정의됨.

**impl**: `as` 캐스트만. `.into()`, `.try_into()`, `.wrapping_*` 등 stdlib 메서드 자체가 없음. **stdlib 본문 부재로 매트릭스 전체 작동 안 함**.

---

## 12. sum type niche 자동/수동 규칙 — gap-impl

i-want-this.txt 라인 277-299:
```
자동 niche:
  Ptr<T>, ConstPtr<T>  null
  bool                 2..=255
  char                 surrogate (0xD800..=0xDFFF)
  enum                 미사용 discriminant
사용자 opt-in:
  #[niche(0)] / #[niche(I32_MIN..=-1)] / ...
stdlib wrapper:
  NonZero<T>, NonNan<F>, Finite<F>
```
**의도**: 풍부한 niche 시스템.

**spec 207**: 정의됨.

**impl**: niche 최적화 미구현. `T | none` 의 sum type만 처리.

---

## 13. 컬렉션 / 복합 리터럴 desugar — gap-impl

i-want-this.txt 라인 762-770:
```
[1,2,3]                  → List<T>
{"a":1, "b":2}           → Dict<K,V>
{1,2,3}                  → Set<T>
(1,"a",true)             → Tuple
0..5                     → Range
0..=5                    → RangeInclusive
1:3, ::2, 1:             → Slice
2i                       → Complex
```
모두 stdlib `#[literal(query)]` 핸들러로.

**spec 605-literal-magic.md**: 정의됨.

**impl**: `[1,2,3]` 만 `ArrayInit` 으로 처리 (fixed-size memref, List 아님). 나머지 리터럴 미구현.

---

## 14. trailing closure — gap-impl

i-want-this.txt 라인 1628-1662 — 광범위:
```
task::spawn { heavy() }      # 0-args 단축
xs.map |x| { x*2 }            # 1+args
with_file(path) |f| { ... }   # 1+args
par::scope |s| { s.spawn { f() } }  # 중첩
```

**spec 408-trailing-closure.md**: 동일.

**impl**: parser.rs:2596, 2634 `trailing_closure: None` 하드코딩. 미파스, silent miscompile (직전 회차 발견, probe `408_trailing_closure` xfail).

---

## 15. 비교 체이닝 — 정렬됨

i-want-this.txt 라인 1167:
```
비교 체인 (a < b < c) 미채택 — (a < b) < c 로 파싱, 타입 에러
```
**spec 302.5**: 동일.

**impl**: 직전 회차에 cmp chain 거부 추가 — i-want-this.txt 의도와 일치.

---

## 16. f-string `${expr}` 동적 spec — drift?

i-want-this.txt 라인 741-749:
```
f"{x:.${prec}f}"                  # 동적 precision
f"{val:${full_spec}}"             # 전체 spec 동적
f"cost: $100"                     # 리터럴 $
```
**의도**: Python nested `{}` 대신 `${...}` 사용.

**spec 107-string-literals.md**: 동적 spec 미정의.

→ **gap-spec**.

---

## 17. spread / 가변 인자 — gap-spec/impl

i-want-this.txt 라인 834-855:
```
variadic: fn f(xs: ...T) — Slice<T>
spread: f(..args) — Tuple/List/Dict spread
다중 spread: foo(..a, ..b, ..c)
sum(..v1, 100, ..v2)
```

**spec**: variadic / spread 정의 미확인.

**impl**: 미구현 추정.

---

## 18. operator dispatch — primitive 가로채기 (gap-impl 핵심)

i-want-this.txt 라인 1161-1163:
```
파서: a + b → <typeof(a) as Add<typeof(b)>>::add(a, b)
core crate (언제나 implicit import) 가 기본 operator (+, -, *, /, <, > 등) 선언
bootstrap: 컴파일러는 먼저 core 의 operator 선언을 수집해 precedence table 구축
```
**의도**: **primitive 도 trait dispatch**. 컴파일러는 operator symbol 자체를 모름.

**spec 0.4 / 301**: 동일.

**impl**: `infix_for_prim` 이 primitive 두 개에 대해선 `PrimOp` 직결 (트레잇 우회). **사용자 의도 핵심 위반**. 직전 audit `audit/hardcoding.md` 1번 항목.

---

## 19. 연산자 자동 prelude import — drift

i-want-this.txt 라인 1162: `core crate (언제나 implicit import) 가 기본 operator 선언`.

**의도**: prelude auto-import.

**impl**: prelude auto-import 미구현 (`library/core/prelude.rok` 빈 파일, driver 자동 import 메커니즘 없음). 사용자가 명시한 "생략" 사항.

---

## 20. 모듈 매핑 — 정렬됨

i-want-this.txt 라인 549-550 / 1171-1175:
```
단일 파일: foo.rok 만 (서브모듈 없음)
폴더 모듈: foo.rok + foo/*.rok (Rust 2018+)
foo/ 만 있고 foo.rok 없으면 ERROR
```
**spec 504**: 동일.
**impl**: 작동 (직전 회차 검증).

---

## 21. typed throws — gap-impl

i-want-this.txt 라인 1185-1191:
```
fn foo() -> T                      # non-throwing
fn foo() throws -> T               # untyped (any Error)
fn foo() throws (E) -> T           # typed single
fn foo() throws (A | B | C) -> T   # typed sum type
```

**spec 414-throws.md**: 동일.

**impl**: throws 키워드 인식만 (`is_throws: bool`). 의미 미구현.

---

## 22. RokJitSession (REPL/JIT) — gap-impl

i-want-this.txt 라인 445-533: 매우 상세한 JIT 세션 구조 (RokJitSession, SpecKey, Cell, ResourceTracker, ORCv2, undo 등).

**spec 906/907**: 정의됨.

**impl**: JIT 자체 0% (직전 audit).

---

## 23. RHIR bytecode + .a 패키지 포맷 — gap-impl

i-want-this.txt 라인 377-444: `.a` 단일 archive, `.rok.hir` (RHIR bytecode), `.rok.meta`, symbol mangling `_N<pkg_hash_8>_<path>_<name>_<typehash_16>`.

**spec 903/904/905**: 정의됨.

**impl**: 0% (직전 audit). impl 의 mangling 은 단순 `{ty}__{name}` 형태로 spec과 i-want-this.txt 둘 다 위반.

---

## 24. 사용자 정의 키워드 / Unicode 연산자 — gap-impl

i-want-this.txt 라인 759:
```
Unicode 연산자: 별도 lexer 처리 없음 — stdlib 의 #[infix/prefix/postfix] 로 등록
```
i-want-this.txt 라인 1153: `#[infix("≤", prec = 8, none)]` — Unicode alias.

**impl**: ops.rok에 `≡` `≠` `≤` `≥` 부분 등록됨. 동작 부분 검증.

---

## 25. 파싱 모호성 — { ... } 처리

i-want-this.txt 라인 1656-1662:
```
- 제어 키워드 뒤 { ... } = 제어 본체
- 함수 호출 뒤 { ... } = trailing closure (0-args)
- x = { ... }; = 블록 표현식
- a | b 와 fn() |x| { } 구분: fn 호출 직후만 trailing closure
- 블록은 기본 { body } ≡ || body
```
**의도**: **블록은 기본으로 0-args closure** (이건 큰 의미 변화 — 기존 rok 블록 의미와 다름).

**spec 309-block-expressions.md**: 블록은 표현식. trailing closure는 spec 408. `{ body } ≡ || body` 라는 강한 동등성은 명시 안 됨.

→ **사용자 의도와 spec 미묘한 차이**. 사용자 의도가 더 강함 (블록이 closure로 자동 desugar).

---

## 26. 블록 본문 안 assignment 종결자 — gap-impl

i-want-this.txt 라인 1466 예제: `let f = || { count = count + 1 };` — `;` 없음.

**spec 3.9.1 BNF**: stmt 는 `;`로 끝. trailing 은 식.

→ **i-want-this.txt 예제와 spec 3.9.1 모순**. spec strict 해석으로는 예제가 invalid.

**impl**: 직전 회차에 trailing-position assignment의 `;` 생략 허용 추가. 사용자 의도에 맞춤.

---

## 27. 비동기 — async/await/yield 3중 형태

i-want-this.txt 라인 1372-1403:
```
async fn / async { } / async || { }
yield fn / yield { } / yield || { }
async yield fn / async yield { } / async yield || { }
```
**의도**: 매우 상세한 3*3 매트릭스.

**spec 412/413**: 동일.

**impl**: parser는 `async`/`yield` 키워드만 인식. 본격 desugar 미구현.

---

## 28. ref 키워드 일관 사용 — gap-impl

i-want-this.txt 라인 1480-1506:
```
1. fn 파라미터: fn increment(ref n: i32)
2. 호출 시 명시: increment(ref x)
3. Closure capture list: [ref count]
```

**spec 407-ref-keyword.md**: 동일.

**impl**: parser가 `ref` 인식 + AST `by_ref: bool`만. 의미 (caller binding 재할당) 미구현.

---

## 29. 분기 결과 자동 합 타입 — gap-impl

i-want-this.txt 라인 1019-1024:
```
- 분기 타입이 다르면 결과는 자동 합 타입 (i32|f64 등)
- match trailing `,` 허용
- loop 의 break value 로 값 반환
```
**의도**: if/match 가지가 다른 타입이면 결과는 합 타입.

**spec README/3.x**: 동일.

**impl**: `lower_match` 가 첫 가지 타입을 결과 타입으로 사용. 다른 가지 타입이 다르면 silent — **잠재 silent miscompile**.

---

## 30. 메모리 / 컨테이너 / 동시성 stdlib — 거의 전무

i-want-this.txt 라인 569-578:
```
List, Dict, Set, OrderedDict, OrderedSet, Tuple
Array<T,N>, Matrix<T>, Tensor<T>, Range<T>
str, String
Slice<T>, Ptr<T>, ConstPtr<T>
Atomic, Mutex, RwLock, Cell, Channel
```

**spec**: 부분 정의.

**impl**: 0개 구현. trait 시그니처만 (직전 회차에 27 lang slot 등록됨).

---

## 31. par / task / thread / channel API — gap-impl

i-want-this.txt 라인 1408-1419 + 1593-1626:
- `task::spawn / race / join / timeout / yield_now / sleep`
- `thread::spawn`
- `par::for_each / map / reduce / join / scope`
- `channel::<T>()`, `stream::merge / zip`
- 공유 동시성: `Atomic<T>`, `Mutex<T>`, `RwLock<T>`, `Cell<T>`, `Channel<T>`

**spec**: 부분 정의 (706-scheduler, 707-io-and-timer 등).

**impl**: 모두 stub (`runtime/rokr/src/lib.rs` 의 `rok_task_*`, `rok_par_*` 가 nullptr/no-op).

---

## 32. 16-byte object header — gap-impl

i-want-this.txt 라인 1300-1303:
```
offset 0: type_id u32
offset 4: gc_flags u32
offset 8: gc_word u64
offset 16: payload
```

**spec 701**: 동일.

**impl**: malloc 직접 사용, 헤더 구조 없음.

---

## 33. SIMD / target 매트릭스 — stdlib 마일스톤 보류 (2026-04-30)

i-want-this.txt 라인 1769-1775:
```
x86_64: SSE/AVX/AVX-512
aarch64: NEON / SVE
i686: SSE2 (baseline)
armv7: NEON
wasm32: WASM SIMD128
std::simd portable_simd 사용
```

**상태**: i-want 의 내용은 (a) 플랫폼 ISA 매트릭스, (b) `std::simd::Simd<T, N>`
stdlib API 채택, (c) compiler multiversioning 정책 3가지 영역이 섞여 있음.
가장 큰 부분 (b) 가 stdlib 영역이고, (a)/(c) 도 stdlib API 없이는 의미가
공중에 뜸. → **stdlib SIMD layer 마일스톤 시작 시 spec 동시 작성** (현재
gap-spec 으로 분류는 정확하지 않음 — stdlib 의존성이 더 큼).

**spec/impl**: SIMD 미구현.

---

## 34. compiler ↔ runtime 의존성 0 원칙 — 정렬됨

i-want-this.txt 라인 170-181:
```
- compiler/* 는 runtime/* 를 [dependencies] 에 쓸 수 없음
- runtime/* 는 compiler/* 를 [dependencies] 에 쓸 수 없음
- ABI contract 는 spec 문서에만 존재 (Swift 방식)
```

**impl**: 별도 검증 안 했지만 cargo tree로 cross-reference 없음 추정.

---

## 35. CLI 서브명령 매트릭스 — gap-impl

spec 901: 15개 서브명령 (build/run/test/repl/jupyter/fmt/check/lsp/demangle/rhir-text/inspect/new/clean/version/help).

i-want-this.txt: 직접 명시 안 됨, 다만 라인 87-92 에서 REPL/Jupyter/AOT 3 표면 언급.

**impl**: 3 서브명령만 (`emit`, `build`, `run`). 직전 audit `drift.md` 5번에 정리.

---

## 36. extern "C" 자동 주입 (`rok_print_*`, `rok_panic`, `rok_assert`) — drift

**i-want-this.txt**: 자동 주입 메커니즘 명시 안 됨. spec 805 에도 없음.

**impl**: `rokc_driver/src/lib.rs:482 builtin_panic_extern` 이 모든 사용자 파일 앞에 7개 함수 (rok_panic + rok_print_* + rok_assert) 의 extern 블록 자동 주입.

→ **drift**. 사용자 의도엔 이런 자동 주입 없음. stage-1 편의지만 spec 외부.

---

## 종합

| 카테고리 | 건수 | 비고 |
|---|---|---|
| **drift (i-want 없음, spec/impl 추가)** | 5 | 디렉토리 체계, 805 여분 심볼, 자동 extern 주입, CLI emit, prec table 가능성 |
| **gap-spec (i-want 있음, spec 누락/오기)** | 6 | char primitive 분류, pub(shy), f-string 형식, 동적 `${...}`, prec ladder 예시, blocks `{ body } ≡ || body` |
| **gap-impl (i-want+spec 있음, impl 미구현)** | 25+ | f-string, 메타 블록/템플릿, primitive operator dispatch, niche, 컬렉션 리터럴, RHIR/RokJitSession, ref 의미, throws, par/task/thread, 16B header, SIMD, etc. |
| **정렬됨** | 5 | 모듈 매핑, 비교 체이닝 거부, compiler↔runtime 의존성 0, async/yield 키워드, broadcast 토큰 |

**핵심 차이**:
1. **char은 사용자 의도상 stdlib 타입** (impl과 일치). spec 207/211 갱신 필요.
2. **primitive operator도 trait dispatch** 가 사용자 의도. impl이 PrimOp로 가로채는 게 핵심 위반.
3. **메타 블록/템플릿 토큰 시스템 전체 미구현** — 사용자가 매우 상세히 설계했는데 0%.
4. **stdlib 본문 거의 전부 미구현** — List/Dict/Atomic/par/task 등 사용자 의도의 큰 부분이 비어있음.
5. **JIT/REPL/RHIR/.a 포맷 0%** — 사용자 의도의 기본 인프라 (REPL, Jupyter) 가 미작동.

**다음 우선순위 (사용자 의도 정렬도 기준)**:
1. ~~spec 207/211의 char primitive 분류 정정~~ ✓ (2026-04-28)
2. ~~spec 506 pub(shy)~~ — 사용자 폐지 결정으로 제외
3. ~~spec 302.3 prec ladder 예시를 ops.rok 등록값으로 동기화~~ ✓ (2026-04-28)
4. ~~impl primitive operator 를 LangTable lookup 경로로 라우팅~~ ✓ (2026-04-28)
   `lower_infix` / `lower_prefix` 디스패치 순서를 trait dispatch → PrimOp fallback 로
   변경. stdlib 이 `impl Add for i32` 등을 작성하면 자동 활성화.
5. ~~spec 805 자동 주입 부록~~ ✓ (2026-04-28) — 8.5.12 stage-1 진단/편의 심볼.
6. impl prelude auto-import — 사용자 보류 결정.
7. **남은 큰 작업**: 메타 블록 / 템플릿 토큰 시스템 (spec 608/609, impl 0%).
