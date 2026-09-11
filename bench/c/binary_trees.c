// C counterpart of bench/binary_trees.rok (malloc / free instead of a GC).
#include <stdio.h>
#include <stdlib.h>

typedef struct Node {
    struct Node *l, *r;
    long x;
} Node;

static Node *make(long d) {
    Node *n = malloc(sizeof *n);
    n->x = 0;
    n->l = n->r = NULL;
    if (d > 0) {
        n->l = make(d - 1);
        n->r = make(d - 1);
    }
    return n;
}

static long check(const Node *n) { return n->l ? 1 + check(n->l) + check(n->r) : 1 + n->x; }

static void drop(Node *n) {
    if (n->l) {
        drop(n->l);
        drop(n->r);
    }
    free(n);
}

int main(void) {
    const long max = 18, min = 4;
    Node *t = make(max + 1);
    printf("%ld\n", check(t));
    drop(t);
    Node *keep = make(max);
    for (long d = min; d <= max; d += 2) {
        long iters = 1L << (max - d + min), c = 0;
        for (long k = 0; k < iters; k++) {
            t = make(d);
            c += check(t);
            drop(t);
        }
        printf("%ld\n", c);
    }
    printf("%ld\n", check(keep));
    drop(keep);
    return 0;
}
