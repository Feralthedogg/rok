// C counterpart of bench/throw_parse.rok: errors as a status return,
// the value through an out parameter.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

static uint64_t x = 42;
static long *t;
static size_t n, cap, p;
static size_t err_at;

static void push(long v) {
    if (n == cap) {
        cap = cap ? cap * 2 : 16;
        t = realloc(t, cap * sizeof *t);
    }
    t[n++] = v;
}

static void gen(long d) {
    x = x * 6364136223846793005ULL + 1442695040888963407ULL;
    long r = (long)(x >> 33);
    if (d == 0 || r % 4 == 0) {
        push(r % 10);
    } else if (r % 4 == 1) {
        push(-4);
        gen(d - 1);
        push(-5);
    } else {
        gen(d - 1);
        push(-1 - (r / 4) % 3);
        gen(d - 1);
    }
}

static int expr(long *out);

static int factor(long *out) {
    long c = t[p++];
    if (c == -4) {
        if (expr(out)) return 1;
        p++;
        return 0;
    }
    *out = c;
    return 0;
}

static int term(long *out) {
    long v, w;
    if (factor(&v)) return 1;
    while (p < n && (t[p] == -2 || t[p] == -3)) {
        long op = t[p++];
        if (factor(&w)) return 1;
        if (op == -2) {
            v = v * w % 1000003;
        } else {
            if (w == 0) {
                err_at = p;
                return 1;
            }
            v = v / w;
        }
    }
    *out = v;
    return 0;
}

static int expr(long *out) {
    long v, w;
    if (term(&v)) return 1;
    while (p < n && t[p] == -1) {
        p++;
        if (term(&w)) return 1;
        v = (v + w) % 1000003;
    }
    *out = v;
    return 0;
}

int main(void) {
    long sum = 0, errs = 0;
    size_t at = 0, toks = 0;
    for (int k = 0; k < 200000; k++) {
        n = 0;
        gen(12);
        toks += n;
        p = 0;
        long v;
        if (expr(&v)) {
            errs++;
            at += err_at;
            v = 0;
        }
        sum = (sum + v) % 1000003;
    }
    printf("%zu %ld %zu %ld\n", toks, errs, at, sum);
    return 0;
}
