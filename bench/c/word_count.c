// C counterpart of bench/word_count.rok: an open-addressing string table.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum { SLOTS = 1 << 17 };

static struct {
    const char *w;
    size_t n;
    long c;
} tab[SLOTS];
static long distinct;

static uint64_t hash(const char *s, size_t n) {
    uint64_t h = 0xcbf29ce484222325ULL;
    for (size_t i = 0; i < n; i++)
        h = (h ^ (unsigned char)s[i]) * 0x100000001b3ULL;
    return h;
}

static long *slot(const char *w, size_t n) {
    for (uint64_t i = hash(w, n) & (SLOTS - 1);; i = (i + 1) & (SLOTS - 1)) {
        if (!tab[i].w) {
            tab[i].w = w;
            tab[i].n = n;
            distinct++;
            return &tab[i].c;
        }
        if (tab[i].n == n && memcmp(tab[i].w, w, n) == 0)
            return &tab[i].c;
    }
}

static int less(const char *a, size_t an, const char *b, size_t bn) {
    int c = memcmp(a, b, an < bn ? an : bn);
    return c < 0 || (c == 0 && an < bn);
}

int main(void) {
    size_t cap = 1 << 24, len = 0;
    char *text = malloc(cap);
    uint64_t x = 7;
    for (long k = 0; k < 2000000; k++) {
        x = x * 6364136223846793005ULL + 1442695040888963407ULL;
        uint64_t r = (x >> 33) % 50000, id = r * r / 50000;
        len += (size_t)snprintf(text + len, cap - len, "w%llu%c", (unsigned long long)id,
                                k % 16 == 15 ? '\n' : ' ');
    }
    for (size_t i = 0; i < len;) {
        while (i < len && (text[i] == ' ' || text[i] == '\n'))
            i++;
        size_t start = i;
        while (i < len && text[i] != ' ' && text[i] != '\n')
            i++;
        if (i > start)
            ++*slot(text + start, i - start);
    }
    const char *best = "";
    size_t bn = 0;
    long top = 0;
    for (long i = 0; i < SLOTS; i++)
        if (tab[i].w && (tab[i].c > top || (tab[i].c == top && less(tab[i].w, tab[i].n, best, bn)))) {
            top = tab[i].c;
            best = tab[i].w;
            bn = tab[i].n;
        }
    printf("%ld %.*s %ld %ld\n", distinct, (int)bn, best, top, *slot("w1", 2));
    free(text);
    return 0;
}
