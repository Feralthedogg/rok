// C counterpart of bench/spectral_norm.rok.
#include <math.h>
#include <stdio.h>

enum { N = 1000 };

static double a(long i, long j) { return 1.0 / (double)((i + j) * (i + j + 1) / 2 + i + 1); }

static void mul_av(const double *v, double *out) {
    for (long i = 0; i < N; i++) {
        double s = 0;
        for (long j = 0; j < N; j++)
            s += a(i, j) * v[j];
        out[i] = s;
    }
}

static void mul_atv(const double *v, double *out) {
    for (long i = 0; i < N; i++) {
        double s = 0;
        for (long j = 0; j < N; j++)
            s += a(j, i) * v[j];
        out[i] = s;
    }
}

static void mul_atav(const double *v, double *out, double *tmp) {
    mul_av(v, tmp);
    mul_atv(tmp, out);
}

int main(void) {
    static double u[N], v[N], tmp[N];
    for (int i = 0; i < N; i++)
        u[i] = 1;
    for (int i = 0; i < 10; i++) {
        mul_atav(u, v, tmp);
        mul_atav(v, u, tmp);
    }
    double vbv = 0, vv = 0;
    for (int i = 0; i < N; i++) {
        vbv += u[i] * v[i];
        vv += v[i] * v[i];
    }
    printf("%.9f\n", sqrt(vbv / vv));
    return 0;
}
