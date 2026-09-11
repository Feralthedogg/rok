// C counterpart of bench/json_tokenizer.rok.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static char *buf;
static size_t len, cap;

static void put(const char *s) {
    size_t n = strlen(s);
    if (len + n + 1 > cap) {
        cap = (len + n + 1) * 2;
        buf = realloc(buf, cap);
    }
    memcpy(buf + len, s, n);
    len += n;
}

int main(void) {
    uint64_t x = 42;
    char tmp[64];
    for (long i = 0; i < 1000000; i++) {
        x = x * 6364136223846793005ULL + 1442695040888963407ULL;
        long r = (long)(x >> 33), k = r % 8;
        switch (k) {
        case 0:
            snprintf(tmp, sizeof tmp, "{\"key%ld\": ", r % 100);
            put(tmp);
            break;
        case 1:
            snprintf(tmp, sizeof tmp, "%ld, ", r % 100000);
            put(tmp);
            break;
        case 2:
            snprintf(tmp, sizeof tmp, "-%ld.5, ", r % 1000);
            put(tmp);
            break;
        case 3: put("\"str\\\"ing\", "); break;
        case 4: put(r % 3 == 0 ? "true, " : r % 3 == 1 ? "false, " : "null, "); break;
        case 5: put("["); break;
        case 6: put("], "); break;
        default: put("}\n");
        }
    }
    const unsigned char *s = (const unsigned char *)buf;
    long strings = 0, numbers = 0, literals = 0, punct = 0, sum = 0;
    size_t i = 0, n = len;
    while (i < n) {
        unsigned char c = s[i];
        if (c == '"') {
            i++;
            while (i < n && s[i] != '"') {
                if (s[i] == '\\')
                    i++;
                i++;
            }
            i++;
            strings++;
        } else if (c == '-' || (c >= '0' && c <= '9')) {
            int neg = c == '-';
            if (neg)
                i++;
            long v = 0;
            while (i < n && s[i] >= '0' && s[i] <= '9')
                v = v * 10 + (s[i++] - '0');
            if (i < n && s[i] == '.')
                for (i++; i < n && s[i] >= '0' && s[i] <= '9'; i++)
                    ;
            sum += neg ? -v : v;
            numbers++;
        } else if (c >= 'a' && c <= 'z') {
            while (i < n && s[i] >= 'a' && s[i] <= 'z')
                i++;
            literals++;
        } else {
            if (c != ' ' && c != '\n')
                punct++;
            i++;
        }
    }
    printf("%zu %ld %ld %ld %ld %ld\n", n, strings, numbers, literals, punct, sum);
    free(buf);
    return 0;
}
