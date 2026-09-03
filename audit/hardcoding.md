> **STALE — superseded by [AUDIT_2026-10-12.md](AUDIT_2026-10-12.md).** 숫자·줄 번호·경로(현재 `library/{bare,core,std}`, 삭제된 `run_probes.sh`)는 당시 기준이며 현재와 다름. 역사 기록으로만 보존.

# 컴파일러 하드코딩 / 명세 위반 매직 — 전수조사

기준 시점: 2026-04-29 (silent miscompile 차단 회차 후)

## 원칙 (spec 0.4)

> 언어는 표기법만 정의한다. 표기법이 어떤 동작을 의미하는지는 표준 라이브러리에 등록된
> 트레잇 메서드로 desugar 된다.

매핑 메커니즘:
- `#[infix]/#[prefix]/#[postfix]` (607) — 연산자 토큰 ↔ 트레잇 메서드
- `#[lang(...)]` (604) — 컴파일러 슬롯 ↔ stdlib 항목
- `#[literal(...)]` (605) — 복합 리터럴 패턴 ↔ stdlib 핸들러
- `#[keyword(...)]` (606) — stdlib가 등록한 키워드

## 핵심 결함

> [!IMPORTANT]
> 1. **`#[lang(...)]` 메커니즘 자체가 전혀 구현되어 있지 않다.**
>    impl 코드 검색: `lang(`/`#[lang`/`lang_slot`/`LangSlot` — 0 hits in compiler.
> 2. **`#[infix]/#[prefix]/#[postfix]`는 작동하지만 절반만.** 토큰/prec/assoc/method_name
>    등록 + 사용자 `Struct`/`Enum`에 대한 dispatch까지 작동. 그러나 primitive 타입은
>    컴파일러가 가로채서 `PrimOp`로 직결(트레잇 우회), Sum/Tuple/Array/Fn 타입은 dispatch
>    경로 자체가 없음.
> 3. stdlib (`library/core/`)는 ops 트레잇 선언만 200줄, 나머지(List/Dict/Iterator/Range/Index/Slice/Future)는 전무.
>
> 따라서 spec이 "stdlib이 결정"이라 한 의미의 절반은 이미 살아있고, 절반은 컴파일러가 들고 있다.

## 영역별 위반

### 1. 연산자 의미론 — spec 3.1 / 6.4 / 6.7 부분 작동

`+ - * / % == != < > <= >= && || & | ^ ~ << >>` 모두 스펙은 트레잇 dispatch.

**`#[infix]` 메커니즘 상태**: 작동함 (절반).
- `prec.rs:90-94 collect_attr` — `#[infix]/#[prefix]/#[postfix]` 인식
- `prec.rs:157-163` — symbol+prec+assoc+**method_name**까지 `OpEntry`로 저장
- `parser.rs:1985-2028` — PrecTable 사용해서 prec/assoc로 파싱
- `lower.rs:4466 lower_infix` 흐름:
  1. **둘 다 primitive 동일 타입** → `infix_for_prim` (4572) 의 `PrimOp::Add/Sub/...` 직결, **트레잇 우회**
  2. 그 외 → `dispatch_user_op` (4535)
  3. `MethodTarget::Struct/Enum`이면 `method_table[(target, entry.method_name)]` lookup → 메서드 호출 emit
  4. **Sum/Tuple/Array/Fn**이면 `return None` (4544-4547) → fallback to `Const(Unit)` 또는 미지원

| 케이스 | 작동? | 경로 |
|---|---|---|
| `let a: V; let b: V; a + b` (V는 user struct, `impl Add for V`) | ✓ | `dispatch_user_op` → `V::add(a, b)` 호출 |
| `use core::ops::Add; impl Add<V> for V { type Output = V; fn add ... }` | ✓ (2026-04-28) | stdlib trait + assoc type 바인딩 + `+` dispatch까지 end-to-end 작동. probe `209_stdlib_add_trait` 검증 |
| `let a: i32; a + b` | **부분** | PrimOp 직결, 트레잇 우회. spec은 트레잇이라 했지만 의미 동일 (impl만 다름) |
| 사용자 `impl Add<MyOtherType> for i32` | **✗** | primitive 경로가 항상 가로챔 |
| `Color::Red + ...` (Sum 타입) | **✗** | dispatch_user_op이 Sum 미지원 |
| `let f: fn(i32)->i32; f + g` | **✗** | Fn 미지원 |
| `let arr: [i32; 3]; arr + ...` | **✗** | Array 미지원 |
| `&&` `\|\|` short-circuit | ✓ (2026-04-28 수정) | `lower_infix`가 `&&`/`\|\|`를 `if a { b } else { false }` / `if a { true } else { b }` 으로 desugar. probe `302_short_circuit_and/or` PASS |

영향:
- **spec 0.4 약속의 절반은 이미 작동** (사용자 struct/enum의 `impl Add` 등이 호출됨)
- **나머지 절반 미작동**: primitive 가로채기 (사용자가 `impl Add for i32` 등으로 의미 변경 불가), Sum/Tuple/Array/Fn dispatch 부재, short-circuit semantics 손실

### 2. Broadcast 연산자 — spec 3.3 / 110.3 부분 작동

`.+` `.-` `.*` `./` `.%` `.==` `.!=` `.<` `.>` `.<=` `.>=` `.&` `.|` `.^` `.<<` `.>>` 16개.

**ops.rok**: 16개 전부 `#[infix]`로 등록 (직전 회차에 12개 추가).

**dispatch 상태**: 위 1번과 같은 경로 — `dispatch_user_op`이 `Struct`/`Enum` 타입에만 작동.
- 사용자 struct (예: `struct Vec3`)에 `impl DotAdd for Vec3`하면 ✓ 작동해야 함 (검증 안 됨)
- Array/Tuple 타입에 직접 dispatch는 ✗ (해당 타입 매칭 부재)
- primitive 타입에 broadcast는 의미 없음 (spec도 그렇게 약속하진 않음)

### 3. 인덱싱 / 슬라이싱 — spec 3.6 / 6.4 위반

spec 3.6.1: `arr[i]` → `<typeof(arr) as Index<typeof(i)>>::index(arr, i)`.

**impl**: `rokc_hir/src/lower.rs:2435 ExprKind::Index` — `HirExprKind::ArrayIndex { array, index, elem_ty }`로 직접 lowering. `Index` 트레잇 없음.
- 다차원 인덱싱 `arr[i, j]` 미구현
- 인덱스 타입은 `i32` 하드코딩 (`lower.rs:3637 idx_prim = PrimTy::I32`)
- `IndexSet` (쓰기) 트레잇 없음. `arr[i] = v` 도 직접 처리.
- 슬라이싱 `arr[1:3]` 미구현 — `Slice` 트레잇 자체가 없음
- 경계 검사 의미는 spec이 trait 구현에 위임했지만 impl에 trait이 없으니 무관.

### 4. `for` 루프 — spec 3.13.3 / 4.10 / 6.4 위반

spec: `for pat in xs` → `IntoIterator::into_iter` + `Iterator::next`.

**impl**: `rokc_hir/src/lower.rs:3499 lower_for_range` — `start..end` 형태만 처리, while-counter loop으로 직접 desugar. 비-range iter는 `lower_for_array` (`:3616`)로 별도 처리. `IntoIterator` / `Iterator` 트레잇 없음.

영향:
- 사용자가 `impl Iterator for MyType`을 작성해도 `for x in my_value`는 컴파일 안 됨
- `Range`/`RangeInclusive`/`RangeFrom`/`RangeTo`/`RangeFull` 라이브러리 타입 없음 (spec 3.7.2: range는 Range::new 등으로 desugar여야)

### 5. 복합 리터럴 — spec 6.5 위반

spec 6.5: `[1,2,3]` `{a:1,b:2}` `{1,2,3}` `0..5` `0..=5` `1:3` `2i` 모두 stdlib `#[literal(...)]` 핸들러로 dispatch.

**impl**: `#[literal]` 메커니즘 자체 없음 (rokc_parser/prec.rs `collect_attr` — `infix/prefix/postfix`만 인식, `literal` 무시). dict/set 은 파서 단계에서 명시 거부 (probe `605_dict_literal`, `605_set_literal` 둘 다 negative-must-fail-parse).

| 리터럴 | impl 처리 |
|---|---|
| `[1, 2, 3]` | `ExprKind::List` → `HirExprKind::ArrayInit` 직접 lowering, fixed-size memref. spec의 `List<T>` 동적 컬렉션 아님 |
| `{a: 1}` | **명시 거부** (parse 단계). 핸들러 시스템 도입 후 본문 작성 |
| `{1, 2}` | **명시 거부** (parse 단계) |
| `0..5` | `ExprKind::Range` 언어 내장 (parser.rs:1916). `for`에서만 인식. spec의 `Range::new` 호출 desugar 아님 |
| `0..=5` | 동일 — 패턴/range expr만 |
| `1:3` | 슬라이스 미구현 |
| `2i` | 허수 리터럴 미구현 (어휘 단계 거부) |

### 6. `??` 빈자리 합체 — spec 110.3 / 3.8 vs 명시적 하드코딩

spec 110.3은 `??`를 고정 토큰으로 정의.
parser.rs:1979 주석: **"`??` is a language-level operator, not a stdlib trait dispatch"**.

→ **하드코딩 의도적으로 명시**. spec 3.8.3은 `??`의 desugar를 `match { v: T => v, none => default }`로 정의. 의미상 일관됨. 그러나 spec 0.4의 "표기법 → 트레잇 desugar" 일반 원칙과는 어긋남. 의도적 예외이지만 spec과 impl 둘 다 문서화 필요.

### 7. `?.` 옵션 체이닝, `?` 후위 ?-trail — spec 3.8 / 3.14 ↔ impl

spec 3.8.1: `x?.field` → `match x { v: T => v.field, none => none }`.
spec 3.14: `expr?` → 합 타입 빈자리(none) 자동 전파.

**impl**: `parser.rs:2567 QuestionDot`, `parser.rs:2564 TryQ` AST 노드. `lower.rs:2472/2476 desugar_question_dot/desugar_try_q`. — 컴파일러 내부에서 spec 의미대로 desugar (트레잇 dispatch 아닌 직접 변환). spec 자체가 "match로 desugar" 라 했으므로 의미 정렬. 하드코딩이지만 spec 의도와 같음.

### 8. `none` 센티넬 — spec 6.4 위반

spec 6.4.3: `"none_type"` 슬롯을 `#[lang]`으로 stdlib 타입에 부착. 컴파일러는 `none` 리터럴을 그 슬롯의 타입으로 evaluation.

**impl**: `Literal::None` → `ConstVal::None` 하드코딩 (`lower.rs:70`). `rokc_lexer:249 "none" => TokenKind::None` 키워드 직결. stdlib에 `NoneSentinel` 같은 타입 없음. `#[lang("none_type")]` 매핑 없음.

### 9. 숫자 리터럴 접미사 → primitive 매핑 — spec 6.5 / 1.6 위반

spec 1.6.1: 접미사는 lexical 형태만, 의미는 stdlib 결정.

**impl**: `lower.rs:4796 fn parse_int_literal`이 접미사 11종을 PrimTy로 직접 매핑. 무접미사 → `PrimTy::I32` 하드코딩.

```rust
const SUFFIXES: &[(&str, PrimTy)] = &[
    ("isize", PrimTy::Isize), ("usize", PrimTy::Usize),
    ("i64", PrimTy::I64), ("u64", PrimTy::U64), ...
];
.unwrap_or((text, PrimTy::I32));   // 무접미사 디폴트
```

### 10. Primitive 타입 이름 — spec 6.4 위반

spec 0.4.2: 숫자/문자 타입은 stdlib가 정의.

**impl**: `rokc_hir/src/ty.rs:54-68` — `i8 i16 i32 i64 isize u8 u16 u32 u64 usize f32 f64 bool c_char str` 14종 타입 이름이 컴파일러 내부 enum `PrimTy::*`로 직결. stdlib에 이 타입들 정의 없음 (`#[lang("i32_type")]` 등 없음).

ty.rs 주석: "Once the stdlib registers `#[lang(...)]` markers these..." — TODO만 있음.

### 11. 자동 주입 extern — spec / drift

`rokc_driver/src/lib.rs:482 builtin_panic_extern` — 모든 사용자 파일 앞에 7개 함수의 `extern "C"` 블록 주입:

```
rok_panic, rok_assert, rok_print_str, rok_print_i32, rok_print_i64,
rok_print_bool, rok_print_f64
```

**spec 805**에 정의된 심볼은 `rok_panic`만. 나머지 6개는 spec에 없는 stage-1 진단 편의 심볼.
spec은 stdlib에 `display_trait`/`debug_trait`을 정의해서 `f"{x}"`로 출력하라고 함 (605). impl은 print 함수를 직접 노출.

### 12. String 리터럴 = `*const u8` (C 문자열) — spec 위반

spec 1.7: 문자열은 stdlib 타입. spec 6.4: `"display_trait"` / fmt 트레잇.

**impl**: `PrimTy::Str`이 `*const u8` (null-terminated, libc style). `rok_print_str(s: str)` 시그니처는 실제로는 `*const u8`. stdlib `String` / `&str` 타입 없음.

### 13. 가시성 키워드 `pkg` / `sub` — spec 5.6 ↔ impl

spec 5.6: `pub` `pub(pkg)` `pub(sub)` 가시성 단계. `pkg`/`sub`는 컨텍스트 키워드.

**impl**: `parser.rs:1068 "pkg" => Visibility::Pkg, "sub" => Visibility::Sub` 식별자 문자열 비교로 직결. 키워드 등록 메커니즘 없음.

### 14. 복합 대입 desugar — spec 3.4 ↔ impl

spec 3.4: `a += b` → `<T as AddAssign<U>>::add_assign(ref a, b)` (or `Add::add` then assign).

**impl**: `parser.rs:1868 compound_assign_op` — `a += b`를 `a = a OP b`로 단순 desugar. 그 OP는 위 1번대로 `PrimOp::Add` 직결.

### 15. 컴파일러가 모르는 매직 (none-of-the-above)

다음은 spec이 아예 정의 안 했는데 impl이 노출:

- `rok_alloc(size, align) -> usize` — heap 편의 wrapper, spec 805 없음
- `rok_free(ptr)` — 동일
- `rok_load_i32/i64/f64`, `rok_store_i32/i64/f64` — 타입드 메모리 접근
- `rok_print_*`, `rok_write_*` (str/i32/i64/f64/bool/hex 8종) — 진단 출력
- `rok_str_len`, `rok_str_eq` — 문자열 헬퍼
- `rok_assert(cond) -> i32` — 어설션
- `--bootstrap`, `-L libpath::*`, `--rokr` CLI 옵션 — spec 901 없음
- `rokc emit` 서브명령 — spec 901에 없음 (build의 `--emit` 옵션과 중복)

## 매직 부재로 인한 누락 영역

다음은 spec에 정의되어 있지만 impl에 없음 (메커니즘 자체가 없으므로 stdlib 작성 불가):

- `#[lang(...)]` 슬롯 등록 (~30개 슬롯)
- `#[literal(...)]` 컬렉션 리터럴 핸들러 (~7개)
- `#[keyword(...)]` 사용자 키워드 등록
- `#[derive(Eq/Ord/Hash/Display/Debug/Clone)]` 6종
- `#[repr(C/transparent/packed/align/uN)]`
- `#[link]`, `#[inline]`, `#[test]`, `#[cold]`, `#[deprecated]`, `#[doc]`, `#[allow]`/`#[deny]`/`#[warn]`, `#[non_exhaustive]`, `#[must_use]`
- `#[cfg(...)]` 조건부 컴파일, `cfg!()` 식
- `@derive` / `@attribute` 메타 블록 (spec 608)
- 템플릿 토큰 `@Self`/`@field`/`@for_fields`/`@for_variants`/`@apply_if` (spec 609)

## stdlib 본문 누락

`impl/library/core/` (2026-04-28 갱신):
- `lib.rok` — 8 모듈 export
- `ops.rok` — 16 op trait 선언, 모두 `#[lang]` 부착
- `iter.rok` — Iterator + IntoIterator (lang slot 2)
- `index.rok` — Index/IndexSet/Slice (lang slot 3)
- `fmt.rok` — Display/Debug (lang slot 2)
- `marker.rok` — Clone/Eq/Ord/Hash (lang slot 4)
- `future.rok` — Future/Stream (lang slot 2)
- `range.rok` — Range/RangeInclusive/RangeFrom/RangeTo/RangeFull struct (lang slot 0 — `#[literal]` 핸들러용)
- `prelude.rok` — 여전히 빈 파일 (auto-import 메커니즘 미구현)

**lang 슬롯 27개 등록 완료**.

End-to-end 검증 (probe `209_stdlib_add_trait`):
```rok
use core::ops::Add;
impl Add<V> for V { type Output = V; fn add(...) ... }
let c = a + b;   // → Add::add(a, b) dispatch
```
→ stdlib trait + `#[lang]` 등록 + `+` operator 라우팅이 처음으로 사용자 코드에서 작동.

여전히 누락:
- `Int/Float/Bool/Char/Str` 타입 정의 (현재 컴파일러 PrimTy 직결)
- `List/Dict/Set/Tuple` 컬렉션 (현재 ArrayInit 등 직결)
- `Atomic/Mutex/Channel` 동시성
- 트레잇 메서드 본문 (현재 시그니처만)
- prelude auto-import 메커니즘
- `#[literal(...)]` 핸들러 — Range 등이 등록만 되고 와이어업 안 됨

다음 단계는 컴파일러가 등록된 lang 슬롯을 lookup해서 하드코딩을 교체하는 것
(`for` → iterator_trait, `[i]` → index_trait, `none` → none_type 등).

## 종합 (2026-04-29 갱신)

| 위반 카테고리 | 항목 수 | 상태 | 영향 |
|---|---|---|---|
| `#[infix]/#[prefix]/#[postfix]` 메커니즘 | 30+ 연산자 | **부분 작동** (절반) | Struct/Enum dispatch ✓, Tuple/Array/Sum/Fn 도 `MethodTarget::Mangled` 로 dispatch 가능 ✓, primitive 가로챔 (사용자 `impl Add for i32` 변경 불가) |
| `&&` `\|\|` short-circuit | 2 토큰 | ✓ 작동 (2026-04-28) | HIR이 if-식으로 desugar. trait dispatch 경로는 아니지만 의미는 정확 |
| `#[lang]` 메커니즘 | ~30 슬롯 | **골격 추가됨** (2026-04-28) | 속성 인식 + 슬롯 표 수집 + 6.4.6 중복 검출. 아직 컴파일러 소비자가 없음 (none/iterator/index 와이어업 미실행) |
| `#[literal]` 메커니즘 | 7 리터럴 | **부재** (dict/set parse 거부됨) | List/Dict/Set/Range/Slice 컬렉션 리터럴 의미 없음. dict/set 은 silent miscompile 차단 명시 거부 |
| `#[keyword]` 메커니즘 | - | **부재** | 사용자/stdlib 키워드 등록 불가 |
| `#[derive]` | 6 종류 | **명시 거부** (2026-04-29) | HIR 등록 단계에서 explicit error |
| `#[cfg(...)]` | 1 | **작동** (driver 측 filter_items) | true/false 평가 + 분기 한쪽만 살아남음. probe `603_cfg_flag` PASS |
| `#[repr]` 등 나머지 빌트인 속성 | 13+ | **부재** | 인식 안 됨 |
| Iterator desugar | `for` 전부 | **하드코딩** | range counter / array index 직결, IntoIterator 트레잇 부재 |
| Index/Slice desugar | `arr[i]` `arr[1:3]` | **하드코딩** | `Index`/`IndexSet`/`Slice` 트레잇 부재 |
| primitive 타입 | 14종 (i32/f64/...) | **컴파일러 enum** | stdlib 정의 부재, `#[lang]` 매핑 부재 |
| 정수 리터럴 접미사 | 11종 | **하드코딩** | `parse_int_literal`이 SUFFIXES 표로 PrimTy 직결 |
| `none` 센티넬 | 1 | **하드코딩** | `Literal::None` → `ConstVal::None` 직결 |
| spec 외 매직/심볼 | ~30 | **drift** | `rok_print_*`, `rok_alloc`, `rokc emit`, `--bootstrap` 등 |
| stdlib 본문 | ~50 항목 | **부분 (트레잇만)** | trait 시그니처 24개 정의됨, 메서드 구현 본문 / 컬렉션 타입 아직 없음 |

## 핵심 결론

> **메커니즘은 절반만 살아있다.** `#[infix]`는 작동하고 사용자 `Struct`/`Enum`에 대해선
> 트레잇 dispatch까지 이루어진다 — 이 부분은 spec 0.4 약속을 이미 지킨다. 그러나
> `#[lang]`/`#[literal]`/`#[keyword]` 가 부재하고, primitive 타입 의미가 컴파일러에 매여 있고,
> Sum/Tuple/Array/Fn dispatch 경로가 없고, short-circuit이 손실되어 있다. stdlib은 거의 비어 있어서
> 채울 메커니즘이 와도 채울 내용이 없다.

가장 먼저 필요한 것 (우선순위):

1. ~~`&&`/`||` short-circuit 복원~~ ✓ 완료 (2026-04-28).
2. ~~`#[lang(...)]` 속성 인식 골격~~ ✓ 완료 (2026-04-28). `rokc_parser/src/lang.rs:LangTable`,
   `rokc_driver:build_lang_table`. 이제 stdlib이 슬롯 등록 가능.
3. ~~non-Struct/Enum impl 타깃 silent miscompile 막기~~ ✓ 1단계 완료 → ✓ **2단계 완료** (2026-04-28).
   - 1단계: 명시 거부 (silent miscompile 막힘)
   - 2단계: `MethodTarget::Mangled(String)` 추가 + `impl_target_key` 확장 + `ty_mangle` 확장
     → `impl Foo for (i32,i32)`이 실제로 작동, `t.foo()`가 메서드 결과 반환.
     spec 2.9.1의 "type_expr 임의" 약속 실현.
4. **컴파일러 소비자 와이어업** — 등록된 LangTable을 HIR이 실제로 lookup해서
   기존 하드코딩을 교체:
   - `none_type` — `Literal::None` 자리에서 lookup
   - `iterator_trait` + `into_iterator_trait` — `for` desugar
   - `index_trait` — `[i]` desugar
   - `add_trait` 등 — primitive 가로채기 우회 옵션
5. **stdlib에 primitive impl 작성** — `i32::add`, `f64::add` 등을 stdlib 으로
   옮기고 컴파일러는 추론만.
6. ~~`MethodTarget` 확장~~ ✓ 완료 (2026-04-28). `Mangled(String)` 변형 추가, ty_mangle이
   Tuple/Array/Sum/Fn/Closure를 고유한 mangled name으로 매핑.
