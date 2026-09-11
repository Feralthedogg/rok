// C counterpart of bench/fannkuch.rok.
#include <stdio.h>

int main(void) {
    enum { n = 10 };
    long perm[n], perm1[n], count[n];
    for (long i = 0; i < n; i++) {
        perm1[i] = i;
        count[i] = 0;
    }
    long max_flips = 0, checksum = 0, perm_count = 0, r = n;
    for (;;) {
        for (; r != 1; r--)
            count[r - 1] = r;
        for (long i = 0; i < n; i++)
            perm[i] = perm1[i];
        long flips = 0;
        for (long k = perm[0]; k != 0; k = perm[0]) {
            for (long lo = 0, hi = k; lo < hi; lo++, hi--) {
                long t = perm[lo];
                perm[lo] = perm[hi];
                perm[hi] = t;
            }
            flips++;
        }
        if (flips > max_flips)
            max_flips = flips;
        checksum += perm_count % 2 == 0 ? flips : -flips;
        int done = 1;
        for (; r != n; r++) {
            long p0 = perm1[0];
            for (long i = 0; i < r; i++)
                perm1[i] = perm1[i + 1];
            perm1[r] = p0;
            if (--count[r] > 0) {
                done = 0;
                break;
            }
        }
        if (done)
            break;
        perm_count++;
    }
    printf("%ld\nPfannkuchen(%d) = %ld\n", checksum, n, max_flips);
    return 0;
}
