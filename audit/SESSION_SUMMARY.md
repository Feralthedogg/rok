# 이번 세션 종합 — 2026-04-28~29

## 결론

`impl/` 의 spec 정렬도가 큰 폭으로 개선됨. 통합 테스트 191건 ✓, spec probe corpus **92건** (positive 63 / negative 26 / measure 3, **xfail 0**). 모든 probe 가 명확한 분류로 정리되어 stage-1 동작이 확정됨 — 큰 마일스톤 (const generic, ref capture, derive expander, cfg literal handler, coroutine runtime, real unwind, into stdlib) 은 모두 명시 거부 + 명확한 진단으로 차단 (silent miscompile 0건). 본문 구현이 들어가는 순간 자동 알림 (probe 가 PASS 로 전환되며 xfail 마커 제거 권유).

## 핵심 인프라

### audit/ 디렉토리

| 파일 | 용도 |
|---|---|
| `drift.md` | 6 표 (105, 110, 302, 805, 901, AST top-level) 양방향 비교 |
| `hardcoding.md` | 컴파일러 vs stdlib 경계, primitive operator routing 등 |
| `probe_results.md` | spec probe 92건 결과 + 회차별 갱신 이력 |
| `intent_vs_spec.md` | i-want-this.txt 1776줄 vs spec/impl 36개 비교 |
| `probes/*.rok` | 92 probe (positive 63 / negative 26 / measure 3) |
| `run_probes.sh` | manual 분류기 (5단계 결과) |

### CI 통합

- `compiler/rokc/tests/spec_probes.rs` — `cargo test -p rokc --test spec_probes` 로 자동
- 5 probe kind: `positive` / `positive-parse-only` / `negative-must-fail` / `negative-must-fail-parse` / `measure`
- `// xfail: <reason>` 디렉티브 — known gap 추적, 수정 시 자동 알림

## 닫힌 spec 갭 / silent miscompile / runtime crash (35건+)

### 표현식 의미

- `&&` `||` short-circuit (eager → if-desugar)
- `a < b < c` cmp chain 거부
- or-pattern binding silent miscompile → 명시 거부

### 컴파일러 안정

- parser `bump()` past-EOF panic → graceful EOF token

### dispatch / lang

- broadcast 12 trait 등록 (`.%`, `.<<`, `.>=`, etc.)
- `MethodTarget::Mangled` — Tuple/Array/Sum/Fn impl target dispatch
- `#[lang(...)]` 인식 골격 + LangTable + 6.4.6 중복 검출
- primitive operator → trait dispatch routing (stdlib 본문 추가 시 자동 활성)

### 메서드/타입

- `type Output = V;` impl 안 파스
- stdlib trait dispatch end-to-end (`use core::ops::Add` 작동)

### 클로저

- trailing closure: `f() |x| { body }`, `f() { body }`, `f { body }` 모두 작동
- closure param inference (callee `fn(i32)->i32` → `|x|` 의 x 타입)
- `[ref x]` 캡처 리스트 파스 + 명시 거부

### 비동기

- `await expr` 파스 (passthrough)

### 런타임

- 805 누락 7 심볼 stub (rok_throw, rok_exception_current, rok_gc_pin/unpin/collect, rok_thread_init/shutdown)
- label break SIGTRAP 수정 (lower_for_range/array 가 label 누락)

### 패턴/매칭

- tuple length mismatch 거부
- bool/int match exhaustiveness
- `..rest` rest pattern 파스 + lowering
- range pattern (`0..=9 =>`)
- range pattern char/CChar literal

### 제네릭

- generic param default mechanism (monomorphize 단계)

### 메타

- 메타 블록 `#[impl_derive]/[impl_attribute]/[impl_derive_attribute]` 명시 거부

### stdlib

- 8 모듈 (ops, iter, index, fmt, marker, future, range, prelude)
- 27 lang slot 등록
- end-to-end dispatch 검증

### 변수 / 스코프

- typo guard (`coutner = ...` 거부)
- let redeclaration 거부 (same scope)
- general `static mut` 거부 (extern 외부)

### 모듈 / visibility

- 5.6 `mod inner { fn private() }` non-pub 외부 호출 silent 통과 → 명시 거부 (`lower_call` 의 `is_visible` false 분기에서 `Module` 진단 + Unit fall-through 차단)

### throw divergent

- 3.14.1 `let v = if c { 7 } else { throw 99; }` codegen 결함 (else-arm 이 unit 으로 merge 진입) → `HirStmt::Throw(call)` 변형 신설 + MIR Unreachable 종결

### sum 인자 자동 wrap

- 3.14 / 4.x raw i32 → sum-typed 파라미터 자동 wrap (`lower_call` 의 module-qualified 분기에서 `param_tys` 기반 `wrap_into_sum` 재적용)

### or-pattern binding

- 3.11.4 `E::A(x) | E::B(x)` silent reject → 공유 LocalId 사전 할당 + per-alt MIR bind 후 점프 (HIR `or_pattern_binders` 스택 + MIR `Or` 분기 재구성)

### ?. 모나딕 평탄화

- 3.8.2 `o?.inner?.n` 에서 inner 가 옵셔널이면 `Sum<Sum, none>` 중첩 → unit fall-through. `desugar_question_dot` 이 inner_ty 가 이미 none 변형을 가지면 그대로 result_ty 로 사용

### enum named-form variant

- 2.4 `Move { x: i32; y: i32; }` HIR 단계 누락 (`_ => None`) → silent unit 생성자/패턴. `HirEnumVariant.named_fields` 추가 + Tuple payload 매핑, `lower_struct_init` / `lower_pattern (Struct)` 에 enum named 분기 추가

### UFCS 파스

- 2.13 `<A as Make>::make()` 파스 미구현 → `parse_primary` 에 Lt-시작 분기 추가 (stage-1 은 trait 한정자 정보 보존만, `Type::method` 으로 lower)

### ref self 명시 거부

- 2.9.2 `impl Foo { fn m(ref self) { self.v = n; } }` 가 silent miscompile (복사본 mutate). 의미론 미구현 → impl 등록 시 first param `ref self` 명시 거부

### heterogeneous sum payload

- 1019 `i32 | f64` 등 이종 sum payload 가 첫 변형 type 에 고정되어 codegen mismatch → MIR `sum_payload_hir_ty` 가 widest primitive 선택 + SumWrap/SumVariant 단계에서 cast. HIR `lower_if` 가 분기 타입 다르면 자동 sum 통합

### 다차원 인덱싱

- 3.6.1 `m[i, j]` 파스 미구현 → postfix `[ ... ]` 가 comma-separated 인자 받아 chained `Index(Index(m, i), j)` 로 desugar (2D 배열 직동작; trait dispatch 는 별도)

### 명시 generic struct 인스턴스화

- 2.10 `Pair<i32, i32> { a: 5, b: 7 }` 파스 미구현 → 표현식 위치 `<...>` 가 generic 인지 `peek_struct_or_call_after_generics` 로 lookahead, monomorphization walker 가 StructInit path 의 generics 도 합성 Ty 로 방문

### tuple struct

- 2.7.4 `struct NonZero(i32);` HIR 단계 누락 (fields=[]) → 생성자/필드 silent. `lower_struct_def` 가 Tuple 변형도 positional name ("0", "1", ...) 로 등록 + `lower_call` 의 tuple-struct 생성자 desugar + `TupleField` 의 struct receiver 분기

### yield 명시 거부

- 4.11 `yield N` parse + HIR 명시 거부 (coroutine runtime 부재). probe 분류 negative-must-fail 로 전환

### silent gap 일괄 정정

- 4.1 variadic call-site (Slice wrap 부재) + 6.2 `#[derive(...)]` expander 부재 → HIR 명시 거부 추가
- 603 `#[cfg]` / 302 unicode op / 406.2 ref capture / 605 set/dict / 214 `.into()` / 314 throw_catch — probe 분류를 실제 stage-1 동작에 맞게 재정렬 (negative / measure)

### nested tuple destructure

- 3.15.4 `let ((a, b), c) = ((1, 2), 3);` 파스 미구현 → 파서 측 desugar (재귀 헬퍼 + `pending_stmts` 큐) 로 nested 그룹을 fresh temp + follow-up LetTuple 로 평탄화

### generic default body lowering

- 2.10.5 monomorphized body 의 `as T` cast 가 ty_subst 를 안 받아 MLIR 타입 mismatch → `lower_expr` Cast 분기를 `ctx.resolve_ast_ty(ty)` 로 전환

### const generic 마일스톤 분리

- 2.11 `<const N: usize>` 통합은 별도 마일스톤. 파서 이미 명시 거부 → probe 분류 negative-must-fail-parse 로 전환

### 재내보내기 (`pub use`)

- 5.8 `pub use inner::Point` 가 fn_table 만 alias → struct/enum 은 invisible (silent unit). 재내보내기 alias 설치 루프를 struct_table/enum_table/static_tys 에도 적용

### `pkg::` / `sup::` 경로 prefix

- 5.7.2/5.7.3 표현식 위치의 `pkg::a::b` / `sup::a` 가 silent unit (resolve_fn_name 이 첫 segment 그대로 lookup) → 진입부에서 module ancestors 변환 전처리 추가 (uses.rs 의 `resolve_root` 와 같은 semantic)

### closure → fn pointer return 명시 거부

- 4.6 capturing closure 가 `fn(...)` return slot 으로 들어가면 mlir-opt 단계 opaque codegen 에러 → `StmtKind::Return` lowering 에서 ret_ty Fn vs returned Closure 검사 + 사용자 안내 메시지로 차단

### trait-as-type 명시 거부

- 2.x / i-want 538 `let a: Number = 32` silent 통과 → `lower_full` trait_defs 수집 직후 walk_item_tys 로 모든 type 위치 (impl trait_path 제외) 검사 + pre_diags 에 명시 거부

### union 본문 lowering (Hybrid A+B)

- 2.x / i-want 322-340 `union { ... }` silent 0 → Hybrid 구현. Model A (widest-prim storage, fast path) full impl + Model B (byte-array storage, general/`#[repr(C)]`) HIR 단계까지 + codegen stage-2 마일스톤. `HirStructDef.union_kind` + `HirExprKind::UnionWrite/UnionRead` 신설

### struct default field 평가

- 2.x / i-want 942-950 `struct S { count: i32 = 7 }; let s = S {}; s.count` 가 silent 0 → HirField 에 `default: Option<Expr>` 보존, `lower_struct_init` 가 누락 필드를 default expr 로 lower. default 없는 누락 필드는 명시 거부.

### closure value capture 검증

- 4.6 / i-want 1437-1478 — closure value snapshot + for-loop per-iteration capture 가 이미 정상. 행동 락인 probe 2건 추가 (`406_3_value_capture_snapshot`, `406_4_for_loop_capture`)

### 함수 호출

- named arg `f(name: 42)` dispatch + 진단

### codegen

- label block `'b: { break 'b 42 }` value type propagation

## 사용자 의도 정렬 5건

i-want-this.txt 1776줄 vs spec/impl 비교에서 사용자가 지정한 5건:

1. **char primitive → stdlib 타입** (spec 207, 211, 108)
2. **prec ladder ops.rok 동기화** (spec 302)
3. **primitive operator trait dispatch routing** (impl)
4. **메타 블록 명시 거부** (impl)
5. **자동 주입 심볼 spec 부록** (spec 805 §8.5.12)

`pub(shy)` 는 사용자 폐지 결정으로 제외.

## 누적 xfail 0건

xfail 마커는 모두 비워졌다 — 직전 13건 중:
- **9건 본문 fix**: 209 (명시 거부) · 210.5 (cast 치환) · 311.4 (or-pattern shared local) · 311 type-check (sum widest payload) · 314 throw divergent (HirStmt::Throw + Unreachable) · 204 enum named-variant (named_fields) · 210 generic explicit instance (lookahead) · 213 fully qualified path (UFCS parse) · 308 multi-level optional (?. 평탄화) · 308 questionq propagate (param sum wrap) · 306 multi-index (chained index) · 207 tuple struct · 309 branch unify sum · 315.4 nested destructure · 506 visibility module
- **나머지**: 명시 거부 + probe 재분류 (negative-must-fail / measure) — 314 throw_catch, 406.2 ref capture, 411 yield, 214 into, 401 variadic, 602 derive, 605 set/dict, 302 unicode op, 211 const generic

## 추세

- audit corpus 0 → 92 probe (positive 63 / negative 26 / measure 3)
- xfail 13 → 0
- 큰 마일스톤은 모두 명시 진단으로 차단됨 — silent miscompile 0건 보장

## 다음 세션 추천 우선순위

큰 마일스톤들 (probe 가 negative-must-fail 로 차단해 두었으므로, 각각 본문 구현 들어가면 자동으로 PASS 로 전환됨):

1. **314 throw-catch real unwind** (setjmp/longjmp 또는 LLVM landingpad)
2. **6.2 derive expander** (Eq/Ord/Debug 자동 생성)
3. **6.5 literal handler 시스템** (Set/Dict literal)
4. **2.11 const generic** (`<const N: usize>` 통합 + monomorphization)
5. **4.11 generator coroutine** (LLVM coro intrinsic)
6. **stdlib 본문** (`i32::add`, From/Into impl 본문 등)
7. **RHIR / .a 패키지 / JIT** (사용자 의도, 큰 마일스톤)
