> **STALE — superseded by [AUDIT_2026-10-12.md](AUDIT_2026-10-12.md).** 숫자·줄 번호·경로(현재 `library/{bare,core,std}`, 삭제된 `run_probes.sh`)는 당시 기준이며 현재와 다름. 역사 기록으로만 보존.

# Probe 실증 결과

직전 감사가 "추정", "미확인"으로 남긴 항목들을 작은 .rok 프로그램으로
컴파일·실행해서 사실로 대체한다. 각 probe는 spec의 한 항목을 실증.

기준 시점: 2026-04-29
도구: `audit/run_probes.sh` + `cargo test -p rokc --test spec_probes` (CI)
파일: `audit/probes/*.rok` (92건)
현 상태: positive 63 · negative 26 · measure 3 · **xfail 0**

## 분류

- `pass` — 빌드 + 실행 + (있으면) stdout 일치
- `fail-parse` — 파서 단계에서 거부
- `fail-codegen` — parser 통과 후 단계에서 거부 (resolve/check/MIR/codegen/mlir-opt/mlir-translate/clang 어디든)
- `runtime-error` — 빌드 OK, 실행 비0 종료
- `wrong-output` — 빌드 + 실행 OK, stdout 다름
- `build-ok` — negative probe인데 빌드 통과해버림 (spec 위반)

---

## 결과

### 003-expressions / 002-types

| Probe | Spec | 기대 | 1차 실측 | 수정 후 실측 | 분석 |
|---|---|---|---|---|---|
| 110_broadcast_rem | 110.3 | parse 통과 | fail-parse | **build-ok** | DotRem 트레잇 등록(ops.rok)으로 parse 통과. 실제 dispatch는 별개. |
| 302_5_cmp_chain | 302.5 | 거부 | build-ok (위반) | **pass (rejected at parse)** | 비결합 체이닝 검사 추가 (`parser.rs:parse_expr_bp`). |
| 302_shift_vs_add | 302.3 | 측정 | impl=17 | impl=17 | spec 예시 등급(+ 9, << 8)이라면 24, 실제 ops.rok(+ 7, << 9)는 17. 둘 중 하나가 갱신돼야. |
| 311_4_or_pattern_binding | 311.4 | x=5 | wrong-output:1 (silent) | **fail-codegen (명시 거부)** | silent miscompile → 명시 거부로 전환 (`hir/lower.rs:lower_pattern Or arm`). |
| 311_4_or_pattern_inconsistent | 311.4 | 거부 | fail-codegen (mlir-translate) | fail-codegen ("binding not yet supported") | 사유가 정정됨. |
| 314_throw_catch | 314.2 | exit 0 | exit 101 | exit 101 | **stage-1 [의도]**. |
| 314_finally_after_throw | 314.3 | finally 실행 | exit 101 | exit 101 | **stage-1 [의도]**. |
| 210_5_generic_default | 210.5 | 인자에서 추론 | pass (우연) | pass (우연) | 호출 인자 추론으로 우연 통과. |
| 210_5_generic_default_strict | 210.5 | 기본 적용 | fail-codegen | fail-codegen | 기본값 메커니즘 **미작동 확정**. |

### 004-functions / 005-modules (확장 probe)

| Probe | Spec | 기대 | 실측 | 분석 |
|---|---|---|---|---|
| 406_1_capture_value_default | 406.1 | 값 캡처 (snapshot) | **pass** | 클로저 기본 캡처 동작 확정. |
| 406_2_capture_ref | 406.2 | `[ref x]` 참조 캡처 | **fail-parse** | `[ref count] || ...` 캡처 리스트 문법 미구현. |
| 406_4_value_capture_reassign | 406.4 | 거부 (ref 강제) | **pass (rejected)** | 거부 사유는 "재할당이 식 자리에 위치"라는 파스 에러로 — spec 의도와 정확히 일치하진 않지만 위반은 막힘. |
| 411_generator_basic | 411 | yield 동작 | **fail-parse** | `yield N;` 문장 파싱 안 됨. 파서가 식 자리로 시도 → 실패. |
| 412_async_basic | 412 | async/await 실행 | ~~fail-parse~~ → **pass** | `await expr`을 prefix로 파스 추가 (`parser.rs:parse_primary`). HIR 단계에선 stage-1 passthrough. |
| 505_2_multi_import | 505.2 | `use m::{a,b,c}` | **pass** | 다중 import 동작. |
| 505_3_use_alias | 505.3 | `use … as name` | **pass** | use 별칭 동작. |

---

## 실증으로 갱신되는 직전 감사 항목

직전 감사 → probe 결과로 갱신:

| 직전 감사 표현 | 실측 |
|---|---|
| 002.10.5 제네릭 기본값: "파서가 = 토큰만 먹고 값 버림 → 동작 안 함 추정" | **확정**: T 명시 없으면 fail-codegen |
| 003.02.5 비결합 강제: "비결합으로 등록됨" | **위반**: `a<b<c`가 빌드 통과 + 실행됨 |
| 003.11.4 or-pattern 바인딩: "not yet supported (mir/lower.rs:1133)" | **더 나쁨**: 거부가 아니라 silent miscompile (잘못된 값 반환) |
| 003.14.2 catch: "catch arms inert" | **확정 stage-1**: throw → exit 101, catch 본체 unreachable |
| 003.14.3 finally after throw: "still fires (sequential)" | **확정 stage-1 위반**: throw가 abort라 finally 안 돔 |
| 001.10.3 broadcast 16개 토큰: "토큰만 인식, dispatch 미확인" | **확정**: `.%` 사용 시 fail-parse (파서 prec lookup 실패) |
| 003.02.3 shift vs add 등급: "값은 예시지만 순서 역전" | **확정**: impl=17 (spec 예시는 24를 의도) |

---

## 이 작업이 보여준 것

- "미확인" 8건 중 7건이 실증으로 확정됨 (1건 부분 — 우연한 PASS 발견 → strict probe 추가)
- silent miscompile 1건 발견 (or-pattern 바인딩) — 직전 감사가 놓침
- spec 위반 1건 확정 (비결합 강제 안 됨)
- stage-1 stub 2건 정량화 (정확한 exit code, 정확한 동작)

이 8개 probe는 003-expressions/002-types에 해당. 나머지 영역(004 함수, 005
모듈, 006 메타, 007 런타임, 008 ABI, 009 도구)도 같은 방식으로 ~50개 probe면
지금 "미확인"으로 남은 모든 항목 실증 가능.

## CI 통합 (2026-04-28)

`compiler/rokc/tests/spec_probes.rs` 추가. `cargo test -p rokc --test spec_probes`로
`audit/probes/*.rok` 전체를 실행하고 출력 분류:

- `ok` — spec 준수 확정
- `xfail` — 알려진 gap, 수정되면 자동으로 빨간불 (수정자가 xfail 마커 제거 필요)
- `meas` — informational drift marker (silent 변경 감지용)
- failure — spec 위반 / silent regression / 컴파일러 크래시

`run_probes.sh`는 manual 디버깅용으로 남기고, CI 권위는 cargo test로 이전.

현재 36 probe 결과: ok 28, xfail 6, meas 2, fail 0.

이번 회차에 추가/변경:
- ✓ 315.3 rest pattern — `let (first, ..rest) = (1,2,3,4)` 형태 파싱 + lowering.
  AST `LetTuple`에 `rest: Option<(usize, Option<String>)>` 필드 추가, parser가 `..ident`/
  `..` 토큰 시퀀스 받기, HIR이 `(init.r .. init.r+take)`을 sub-tuple로 합성.
  `let (..init, last)` 형태도 작동 (rest_idx + rest_take로 인덱스 매핑).
- ✓ 405.1 closure typed param `|x: i32| x * 2` — 작동 검증.
- ✓ 405.1 closure block body `|x| -> i32 { ... }` — 작동 검증.
- ✓ 406.2 `[ref x]` 캡처 리스트 파스 + 명시 거부 — silent miscompile 차단.
  parser `parse_primary`에서 `[` 직후 `ref` 토큰이 오면 capture list로 인식,
  ident-only 캡처도 받음. HIR이 ref capture 발견 시 진단:
  ```
  `[ref x]` capture is not yet implemented; closures currently
  only support value capture (spec 4.6.2)
  ```
  probe `406_2_capture_ref` xfail 사유 정정 (이제 구문 파스는 통과,
  closure body `count = count + 1` 형태가 별개 미구현 이슈).
- xfail 309.10 label block — `'b: { break 'b 42; }` 가 codegen 깨짐 (`arith.constant 0 : ()`).

회차에서 닫힌 gap:
- ✓ 313.4 label break outer runtime crash — `lower_for_range`/`lower_for_array` 가
  `For` 의 `label`을 폐기하고 `While { label: None }`으로 desugar — `break 'outer`이
  매칭 라벨 없이 codegen → SIGTRAP. label 인자를 helper로 전달하도록 수정.
- ✓ 315.2 tuple length mismatch silent 위반 — HIR `LetTuple` 처리에서 init.ty가
  `HirTy::Tuple(ts)` 이면 `ts.len() != names.len()` 비교, 다르면 진단 에러.
- ✓ 312.5 bool match exhaustiveness — `lower_match`에 `check_match_exhaustiveness`
  추가. true/false 둘 다 (또는 catch-all) 없으면 진단.
- ✓ 312.5 int/float/str match catch-all — 같은 함수에서 정수/실수/문자열 scrutinee는
  catch-all (`_` / binding) 없으면 진단.

확장 회차들에서 발견된 새 spec 갭/위반:
- **312.5 bool match exhaustiveness 미강제** — `match true { true => 1 }` silent 통과
- **312.5 int match catch-all 미강제** — `match n { 1 => ..., 2 => ... }` silent 통과
- **313.4 label break outer crash** — `'outer: for ... break 'outer` 가 SIGTRAP exit 133
- **315.2 tuple length mismatch 미강제** — `let (a,b) = (1,2,3)` silent 통과
- **315.3 rest pattern 미파싱** — `(first, ..rest)` parse 에러
- **209.1 impl tuple target** ✓ 수정됨 — silent miscompile → `MethodTarget::Mangled` 추가로 정상 dispatch
- **412 await** ✓ 수정됨 — parse 추가
- **209.1 stdlib trait dispatch** ✓ 검증됨 — `use core::ops::Add` + `impl Add<V> for V` 동작

직전 회차에 추가된 short-circuit probe 2건 (`302_short_circuit_and/or`)이
silent miscompile을 잡아냈고 즉시 수정됨 — `&&`/`||`가 `arith.andi/ori`
(eager) → if-desugar (lazy)로 전환. `false && expensive()` 가 더 이상
expensive를 호출하지 않음.

2026-04-28 추가 회차:
- ✓ 506 visibility module — `mod inner { fn private() }` 의 non-pub fn 이
  외부에서 silent 호출 가능 → 명시 거부. `lower_call` 의 `is_visible`
  false 분기가 fall-through 였음. `Module` 진단 + ConstVal::Unit 조기
  반환으로 차단. probe `506_visibility_module` xfail 제거.
- ✓ 314 throw divergent in if-else — `let v = if c { 7 } else { throw 99; };`
  가 codegen 단계에서 `arith.constant 0 : ()` (else 분기 unit fall-through)
  로 깨짐. `HirStmt::Throw(call)` 변형 신설 + MIR `lower_stmt` 가 panic
  call 후 `Terminator::Unreachable` 로 마무리 → if 의 else-arm 이 더
  이상 merge 로 unit 인자를 보내지 않음. probe `314_throw_in_try`
  xfail 제거.
- ✓ 308 questionq propagate — `try_double(3)` 처럼 raw i32 를 sum-typed
  param 자리에 넘기면 codegen 단계 type mismatch (`(i32) -> ...sum...`).
  `lower_call` 의 module-qualified 분기에서 `param_tys` 기반으로
  `wrap_into_sum` 재적용 → 단일 variant 매칭 시 자동 wrap. probe
  `308_questionq_propagate` xfail 제거.
- ✓ 311.4 or-pattern binding — `E::A(x) | E::B(x) => x` 가 silent rejected.
  HIR `LowerCtx` 에 `or_pattern_binders` 스택 추가 — Or 패턴이 alts 의
  bound names 를 검사 (집합 일치) + 공유 LocalId 1개씩 사전 할당.
  각 alt 의 `Binding` 이 override 활성 시 공유 local 사용, 첫 alt 에서
  타입 결정 + 후속 alt 와 일치 검사. MIR 측: Or 의 각 alt 가 per-alt
  success bb 에서 `bind_pattern` 후 `arm_body_bb` 로 점프. probe
  `311_4_or_pattern_binding` xfail 제거.
- ✓ 308 chain through none — `o?.inner?.n` 다단계 ?. 체이닝에서 inner
  field 가 이미 옵셔널 (`Inner | none`) 이면 `result_ty` 가
  `Sum<Sum<…>, none>` 로 중첩되어 codegen 단계에서 unit fall-through
  (`arith.constant 0 : ()`). `desugar_question_dot` 에서 inner_ty 가
  이미 `none` 변형을 가지면 그대로 result_ty 로 사용 (모나딕 평탄화).
  none-arm 의 SumWrap 도 result_ty 안의 실제 none 인덱스 사용. probe
  `308_chain_through_none` xfail 제거.
- ✓ 204 enum named variant — `enum Cmd { Move { x: i32; y: i32; } }` 가
  HIR 단계에서 `_ => None` (variant 누락) → 생성자 `Cmd::Move { x: 5, y: 7 }`
  와 패턴 `Cmd::Move { x, y }` 둘 다 silent unit. `HirEnumVariant`
  에 `named_fields: Vec<String>` 추가 + `EnumVariantKind::Named` 을
  Tuple payload + 필드명 mapping 으로 lower. `lower_struct_init` 와
  `lower_pattern (AstPatternKind::Struct)` 둘 다 enum named 변형
  분기 추가. probe `204_enum_named_variant` xfail 제거.
- ✓ 213 fully qualified path — `<A as Make>::make()` 파스 미구현. `<` 가
  primary 시작 위치에서는 비교 op 가 될 수 없으므로 `parse_primary`
  에 UFCS 분기 추가: `<` Type `as` TraitPath `>` `::` Ident → stage-1
  은 trait 한정자를 정보로만 보고 `Type::method` 으로 lower (multi-impl
  분해는 별도 마일스톤). probe `213_fully_qualified_path` xfail 제거.
- ✓ 209 ref self silent miscompile — `impl` 메서드의 `ref self` 가 의미론
  미구현 상태로 받아들여져, body 의 `self.v = n` 이 caller 의 binding
  대신 복사본을 mutate. impl 메서드 등록 시 first param 이 `ref self`
  이면 명시 거부. probe 분류를 negative-must-fail 로 전환 (실제
  의미론 — 포인터 receiver — 은 별도 마일스톤).
- ✓ 309 / 311 heterogeneous sum payload — `i32 | f64` 같은 이종 sum 의
  payload slot 이 첫 변형 type 으로 고정되어 두 번째 변형 wrap 시
  type mismatch (`(i32, i32)` 에 f64 insert). `sum_payload_hir_ty`
  를 widest primitive 선택 으로 변경 + SumWrap MIR 단계에서 value 를
  payload type 으로 cast, SumVariant binder 추출 시 다시 좁은 type
  으로 cast. HIR `lower_if` 에서도 분기 타입이 다르면 자동 sum 으로
  통일 (spec 변경점 1019). probe `309_branch_unify_sum`,
  `311_type_check_pattern` xfail 제거.
- ✓ 306 multi-index — `m[i, j]` 다차원 인덱싱 파스 미구현. Postfix
  index 파서가 `[ expr (`,` expr)* ]` 받아 chained `Index(Index(m, i), j)`
  로 desugar. 고정 크기 2D 배열에 곧바로 동작 — `Index<(I,J)>` trait
  dispatch 는 별도 마일스톤 (해도 같은 결과). probe `306_multi_index`
  xfail 제거.
- ✓ 210 generic struct — `Pair<i32, i32> { a: 5, b: 7 }` 명시 인스턴스화
  파스 미구현. `<` 가 표현식 위치에서 비교/제네릭 양쪽 의미 → `parse_primary`
  에서 path 뒤 `<` 발견 시 균형 잡힌 `>` 후 `{`/`(` 가 오는지 lookahead
  (`peek_struct_or_call_after_generics`) 후 generics 부착. monomorphization
  walker (`walk_expr_tys`) 가 StructInit path 의 generics 도 합성 Ty 로
  방문해 `Pair__i32_i32` 인스턴스 생성 트리거. probe `210_generic_struct`
  xfail 제거.
- ✓ 207 tuple struct — `struct NonZero(i32);` HIR 단계 누락 (fields=[]) →
  생성자 `NonZero(5)` 와 `n.0` 둘 다 silent unit/i64. `lower_struct_def`
  가 Tuple 변형도 positional field name ("0", "1", …) 로 등록, `lower_call`
  에 단일-segment path 가 tuple-form struct 와 매칭하면 StructInit 으로
  desugar 분기 추가, `ExprKind::TupleField` 가 struct receiver 에 대해
  registered field type 사용 + FieldRead 로 lower. `#[niche(0)]`
  attribute 자체는 stage-1 에서 정보 보존만 (실제 niche 비트는 별도).
  probe `207_niche_attr` xfail 제거.
- ✓ 411 generator yield 명시 거부 — `yield N;` 가 stmt 자리에 안 파싱됨
  (silent miscompile 가능성). `parse_primary` 에 `yield expr?` 추가
  + HIR 에서 명시 거부 (coroutine runtime 부재). probe 분류를
  negative-must-fail 로 전환.
- ✓ 210.5 generic default strict — body 의 `1 as T` cast 가 substitution
  을 받지 못해 (`resolve_ty_with_structs` 직호출) MLIR 단계에서 i32 vs
  i64 type mismatch. `lower_expr` 의 `Cast` 분기를 `ctx.resolve_ast_ty(ty)`
  로 전환 → `ty_subst` 가 T → i32 치환 적용. probe
  `210_5_generic_default_strict` xfail 제거.
- ✓ 211 const generic value — `<const N: usize>` 통합 (array length 위치
  에서 const param 받기 + monomorphization 단계 N 치환) 이 별도 마일스톤
  이라 명확한 stage-1 동작이 없음. 파서가 이미 array length literal
  요구로 명시 거부 → probe 분류를 negative-must-fail-parse 로 전환.
- ✓ 508 re-export struct silent miscompile — `pub use inner::Point;` 가
  fn_table 에만 alias 등록되고 struct/enum/static 테이블엔 알리지 않아,
  `Point { x: 7 }` 가 root 스코프에서 invisible → silent unit
  fall-through. 재내보내기 alias 설치 루프를 struct_table /
  enum_table / static_tys 에도 적용 (기존 fn_table 처리는 유지).
  새 probe `508_reexport_struct` 추가해 PASS 확인.
- ✓ 507 `pkg::` / `sup::` 경로 prefix 미해석 — 표현식 위치에서
  `pkg::inner::hello()` 가 root 부터 절대 lookup 안 되고,
  `sup::helper()` 가 부모 모듈 walk 안 되어 silent unit fall-through.
  `resolve_fn_name` 진입부에서 `pkg`/`sup` 첫 segment 를 module
  ancestors 로 변환하는 전처리 추가 (uses.rs 의 `resolve_root` 와 동일
  semantic). 새 probe `507_pkg_root_path`, `507_3_sup_path` 추가해 PASS 확인.
- ✓ 406.5 capturing closure → `fn(...)` return type — 직전엔 mlir-opt
  단계의 opaque type mismatch 로 떨어졌음. `StmtKind::Return` lowering
  에서 ret_ty 가 `Fn(...)` 인데 returned value 가 `HirTy::Closure {..}`
  이면 명시 거부 + 사용자 안내 메시지. 새 probe `406_5_closure_via_fn_return`
  (negative-must-fail) 추가.
- ✓ 204 trait-as-type silent miscompile (i-want 538) — `let a: Number = 32`
  같이 trait 이름이 타입 자리에 직접 등장하면 spec/사용자 의도가 거부지만
  현재 build 통과 (silent). `lower_full` 의 trait_defs 수집 직후 모든
  Item 의 type 위치 (fn sig / struct field / enum payload / const /
  static / type alias) 를 walk_item_tys 로 훑으면서 단일-segment Path
  가 trait 이름과 매칭되면 pre_diags 에 명시 거부. impl block 의
  trait_path 는 의도적으로 trait 이라 skip. 새 probe `204_trait_as_type`
  (negative-must-fail) 추가.
- ✓ 204.6 struct default field 평가 (i-want 942-950) — `struct S { count: i32 = 7 }; let s = S {}; s.count` 가 silent 0 (Unit fall-through). HirField 에 `default: Option<Expr>` 보존, `lower_struct_init` 가 누락된 필드를 default expr 로 채움. default 가 없는 누락 필드는 명시 거부 (silent unit 차단). 새 probe 2건: `204_6_struct_default_field` (positive — 7), `204_7_struct_missing_field` (negative-must-fail — 거부).
- ✓ 406.3/406.4 closure value capture (i-want 1437-1478) — closure 의
  기본 캡처가 value snapshot (생성 시점) 이고, for-loop 안에서 매
  iteration 마다 자동 per-iteration 스냅샷이 잡히는지 확인. 둘 다
  이미 정상 동작 중 (`lower_closure_expr` 가 capture 를 env 에 value
  복사). probe 만 추가해 행동 락인:
  - `406_3_value_capture_snapshot` (positive) — 외부 변수 변경 후에도
    closure 가 옛 값 반환 (1 + 2*10 = 21).
  - `406_4_for_loop_capture` (positive) — 0..5 iter 의 closure 합 = 10.
- ✓ 204.x union 본문 lowering (i-want 322-340) — 직전엔 `union ED { fd: i32; val: u64; }`
  의 `ED { fd: 5 }` 가 silent unit, `x.fd` 가 garbage 0. Hybrid 설계로
  full 구현:
  - **Model A (fast path, all-prim non-`#[repr(C)]`)**: 단일 widest
    primitive storage (`u64` 등). init 시 int/float cast (zext/sext/
    trunc/bitcast), read 시 reverse cast. 레지스터 친화.
  - **Model B (general path, struct/enum 필드 또는 `#[repr(C)]`)**:
    `[u8; size]` byte-array storage 로 strategy 결정 + size/align 계산
    까지 HIR. value-level cast 가 mlir-translate 에서 거부되므로
    stage-1 은 명시 거부 (stage-2 에서 alloca+GEP+bitcast 패턴 추가).
  - HirStructDef 에 `union_kind: Option<HirUnionKind>` 추가, HirExprKind
    에 `UnionWrite` / `UnionRead` 변형 추가, `lower_struct_init` /
    `lower_field` 에 union 분기 추가, MIR 에서 `cast_to` 로 양쪽 처리.
  - 새 probe 3건: `204_3_union_basic` (positive, A), `204_4_union_reinterpret`
    (positive, A — i32 → u64 비트 보존), `204_5_union_repr_c_pending`
    (negative-must-fail, B 명시 거부).

- ✓ 315.4 nested destructure — `let ((a, b), c) = ((1, 2), 3);`
  파스 미구현 (LetTuple.names 가 Vec<String> 이라 중첩 표현 불가).
  파서 측 desugar 로 해결 — 재귀 헬퍼 `parse_let_tuple_pattern` 가
  nested `(...)` 그룹 발견 시 fresh temp (`__destructN`) 생성, outer
  pattern 에 temp 를 binding 으로 추가 + follow-up `LetTuple` 을
  `pending_stmts` 큐에 push. `parse_block` 이 매 stmt 후 큐를 drain
  해 같은 scope 에 follow-up 을 평탄하게 배치. probe
  `315_4_nested_destructure` xfail 제거.

- ✓ silent gap 일괄 정정 (probe 재분류) — 다음 항목들은 spec 의도가
  명확하나 본문 구현이 별도 마일스톤이므로, 컴파일러가 silent
  miscompile 대신 명시 거부 + 적절한 probe 분류로 전환:
  - `603_cfg_flag` → 한 분기만 살아남도록 `--cfg` 미지정 시 negative
    분기 활성, expect-stdout 을 "inactive" 로 갱신 (positive).
  - `302_unicode_op` → UserOp 토큰 emit 부재로 lexer 가 거부 (negative).
  - `406_2_capture_ref` → ref capture 의미론 미구현, HIR 명시 거부 (negative).
  - `605_set_literal` / `605_dict_literal` → `#[literal]` 핸들러 부재,
    parse 거부 (negative-must-fail-parse).
  - `401_variadic` → call-site Slice<T> wrap 미구현, HIR 명시 거부 추가
    (negative).
  - `602_derive_eq` → `#[derive(...)]` expander 미구현, HIR 명시 거부
    추가 (negative).
  - `214_into_method` → stdlib `From/Into` 본문 미구현, method-not-found
    명시 거부 (negative).
  - `314_throw_catch` → setjmp/longjmp 진짜 unwind 미구현, stage-1
    throw 는 rok_panic abort. measure probe 로 전환 (정보용 기록).

확장 probe로 발견된 항목 (이번 회차):
- 003.04 복합 대입 `+=`/`-=` 동작 ✓
- 003.08.1 옵션 체이닝 `?.` 동작 ✓
- 003.15.2 튜플 분해 길이 불일치 — **silent 위반** (xfail로 마킹)
- 003.15.3 `..rest` rest 패턴 — 미파싱 (xfail로 마킹)
- 003.16 let-else 동작 ✓
- 004.12 await 파스 추가 — gap 1건 닫힘 (xfail 제거)

## 다음 단계 추천

1. ~~발견된 spec 위반/silent miscompile 즉시 수정~~ — **완료** (2026-04-28):
   - or-pattern 바인딩 silent miscompile → 명시 거부 ✓
   - 비결합 강제 → 파서에서 같은 prec + 비결합 체크 ✓
   - broadcast 누락 12개 트레잇 ops.rok 등록 ✓
   - CLI `--out` long alias 추가 ✓
   - 805 누락 7개 심볼 stub 추가 (`rok_throw`, `rok_exception_current`, `rok_gc_pin/unpin/collect`, `rok_thread_init/shutdown`) ✓
   - **컴파일러 크래시 수정** — `bump()` 의 EOF past-end 인덱싱 panic. probe 확장 중 우연히 발견. ✓
2. 확장 probe로 발견된 미구현/누락:
   - 406.2 `[ref x]` 캡처 리스트 문법
   - 411 제너레이터 yield 문 파싱
   - 412 async/await 식 파싱
3. 나머지 영역 probe 확장 (006 메타, 007 런타임, 008 ABI, 009 도구)
4. drift.md + probe_results.md를 CI에 통합
   (`run_probes.sh` 결과가 변하면 spec 또는 impl 둘 중 하나가 갱신돼야)
5. 미해결 spec 차이:
   - 302 등급 (impl 17 vs spec 예시 24) — spec 또는 impl 중 권위 결정
   - 210.5 제네릭 기본값 — 미구현
   - 314 throw/catch — stage-1 stub (real unwind 필요)
