// C counterpart of bench/nbody.rok.
#include <math.h>
#include <stdio.h>

#define N 5

static double x[N], y[N], z[N], vx[N], vy[N], vz[N], m[N];

static double energy(void) {
    double e = 0.0;
    for (int i = 0; i < N; i++) {
        e += 0.5 * m[i] * (vx[i] * vx[i] + vy[i] * vy[i] + vz[i] * vz[i]);
        for (int j = i + 1; j < N; j++) {
            double dx = x[i] - x[j], dy = y[i] - y[j], dz = z[i] - z[j];
            e -= m[i] * m[j] / sqrt(dx * dx + dy * dy + dz * dz);
        }
    }
    return e;
}

int main(void) {
    const double pi = 3.141592653589793, solar = 4 * pi * pi, dpy = 365.24;
    double ix[N] = {0, 4.84143144246472090e+00, 8.34336671824457987e+00, 1.28943695621391310e+01, 1.53796971148509165e+01};
    double iy[N] = {0, -1.16032004402742839e+00, 4.12479856412430479e+00, -1.51111514016986312e+01, -2.59193146099879641e+01};
    double iz[N] = {0, -1.03622044471123109e-01, -4.03523417114321381e-01, -2.23307578892655734e-01, 1.79258772950371181e-01};
    double ivx[N] = {0, 1.66007664274403694e-03, -2.76742510726862411e-03, 2.96460137564761618e-03, 2.68067772490389322e-03};
    double ivy[N] = {0, 7.69901118419740425e-03, 4.99852801234917238e-03, 2.37847173959480950e-03, 1.62824170038242295e-03};
    double ivz[N] = {0, -6.90460016972063023e-05, 2.30417297573763929e-05, -2.96589568540237556e-05, -9.51592254519715870e-05};
    double im[N] = {1, 9.54791938424326609e-04, 2.85885980666130812e-04, 4.36624404335156298e-05, 5.15138902046611451e-05};
    for (int i = 0; i < N; i++) {
        x[i] = ix[i];
        y[i] = iy[i];
        z[i] = iz[i];
        vx[i] = ivx[i] * dpy;
        vy[i] = ivy[i] * dpy;
        vz[i] = ivz[i] * dpy;
        m[i] = im[i] * solar;
    }
    double px = 0, py = 0, pz = 0;
    for (int i = 0; i < N; i++) {
        px += vx[i] * m[i];
        py += vy[i] * m[i];
        pz += vz[i] * m[i];
    }
    vx[0] = -px / solar;
    vy[0] = -py / solar;
    vz[0] = -pz / solar;
    printf("%.9f\n", energy());
    const double dt = 0.01;
    for (int step = 0; step < 1000000; step++) {
        for (int i = 0; i < N; i++)
            for (int j = i + 1; j < N; j++) {
                double dx = x[i] - x[j], dy = y[i] - y[j], dz = z[i] - z[j];
                double d2 = dx * dx + dy * dy + dz * dz;
                double mag = dt / (d2 * sqrt(d2));
                vx[i] -= dx * m[j] * mag;
                vy[i] -= dy * m[j] * mag;
                vz[i] -= dz * m[j] * mag;
                vx[j] += dx * m[i] * mag;
                vy[j] += dy * m[i] * mag;
                vz[j] += dz * m[i] * mag;
            }
        for (int i = 0; i < N; i++) {
            x[i] += dt * vx[i];
            y[i] += dt * vy[i];
            z[i] += dt * vz[i];
        }
    }
    printf("%.9f\n", energy());
    return 0;
}
