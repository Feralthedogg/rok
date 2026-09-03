#!/usr/bin/env bash
# probe 분류기. 각 probe를 rokc로 빌드/실행하고 결과를 분류한다.
# 분류:
#   pass             — 빌드 + 실행 + (있으면) stdout 일치
#   fail-parse       — rokc 빌드가 parse 단계에서 실패
#   fail-codegen     — rokc 빌드가 parse 통과 후 실패 (resolve/check/MIR/codegen)
#   runtime-error    — 빌드 OK, 실행 시 비0 종료 (expect-exit와 다른)
#   wrong-output     — 빌드 + 실행 OK, stdout 다름
#
# probe 메타데이터:
#   // spec: <id>
#   // probe: positive | negative-must-fail | negative-must-fail-parse | measure | positive-parse-only
#   // expect-exit: N
#   // expect-stdout: ...

set -u
cd "$(dirname "$0")/.."  # impl/

BOOTSTRAP="library/core/lib.rok"
ROKR="target/debug/librokr.a"
ROKC="target/debug/rokc"
TMP="target/probe_tmp"
mkdir -p "$TMP"

if [[ ! -x "$ROKC" ]]; then
    echo "rokc not built; run 'cargo build -p rokc' first" >&2
    exit 1
fi
if [[ ! -f "$ROKR" ]]; then
    echo "librokr.a not built; run 'cargo build -p rokr' first" >&2
    exit 1
fi

printf '%-50s %-25s %-15s %s\n' "PROBE" "EXPECTED" "ACTUAL" "DETAIL"
printf '%-50s %-25s %-15s %s\n' "-----" "--------" "------" "------"

for src in audit/probes/*.rok; do
    name=$(basename "$src" .rok)
    expected=$(grep -m1 -oE 'probe: *[a-z-]+' "$src" | sed 's/probe: *//')
    expected=${expected:-positive}

    exe="$TMP/$name"
    build_log="$TMP/$name.build.log"

    if "$ROKC" build --bootstrap "$BOOTSTRAP" --rokr "$ROKR" -o "$exe" "$src" \
            >"$build_log" 2>&1; then
        # build succeeded
        if [[ "$expected" == "negative-must-fail" || "$expected" == "negative-must-fail-parse" ]]; then
            printf '%-50s %-25s %-15s %s\n' "$name" "$expected" "BUILD_OK" \
                "spec violation: should have failed"
            continue
        fi
        if [[ "$expected" == "positive-parse-only" ]]; then
            printf '%-50s %-25s %-15s %s\n' "$name" "$expected" "BUILD_OK" \
                "parse+codegen ok"
            continue
        fi

        # run it
        actual_stdout=$("$exe" 2>&1)
        actual_exit=$?
        expected_exit=$(grep -m1 -oE 'expect-exit: *[0-9]+' "$src" | grep -oE '[0-9]+')
        expected_stdout=$(awk '/^\/\/ expect-stdout:/{flag=1;next} flag && /^\/\/ /{sub(/^\/\/ ?/,"");print;next} flag{exit}' "$src")

        if [[ -n "$expected_exit" && "$actual_exit" != "$expected_exit" ]]; then
            printf '%-50s %-25s %-15s %s\n' "$name" "$expected" "RUNTIME_ERR" \
                "exit=$actual_exit (want $expected_exit)"
            continue
        fi
        if [[ -n "$expected_stdout" ]]; then
            if [[ "$actual_stdout" != "$expected_stdout" ]]; then
                printf '%-50s %-25s %-15s %s\n' "$name" "$expected" "WRONG_OUTPUT" \
                    "stdout differs"
                continue
            fi
        fi
        printf '%-50s %-25s %-15s\n' "$name" "$expected" "PASS"
    else
        # build failed — classify parse vs later
        if grep -q "\[parse\]" "$build_log"; then
            stage="FAIL_PARSE"
        else
            stage="FAIL_CODEGEN"
        fi
        first_err=$(grep -m1 "^error:" "$build_log" | sed 's/^error: //' | cut -c1-60)
        if [[ "$expected" == "negative-must-fail" && "$stage" =~ FAIL ]]; then
            printf '%-50s %-25s %-15s %s\n' "$name" "$expected" "PASS" \
                "rejected as expected ($stage)"
        elif [[ "$expected" == "negative-must-fail-parse" && "$stage" == "FAIL_PARSE" ]]; then
            printf '%-50s %-25s %-15s %s\n' "$name" "$expected" "PASS" \
                "rejected at parse"
        elif [[ "$expected" == "negative-must-fail-parse" && "$stage" != "FAIL_PARSE" ]]; then
            printf '%-50s %-25s %-15s %s\n' "$name" "$expected" "$stage" \
                "rejected but not at parse: $first_err"
        else
            printf '%-50s %-25s %-15s %s\n' "$name" "$expected" "$stage" "$first_err"
        fi
    fi
done
