//! libm behind `rok_`-prefixed symbols for core's `f32` / `f64` methods
//! (stdlib spec 2.1.4). core cannot declare `floor` / `log` itself: an
//! extern's name is global in rok, so a user `fn log` would clash. The
//! driver links `-lm`.

macro_rules! libm {
    ($($rok:ident = $c:ident($($a:ident),+) : $t:ty;)*) => {
        unsafe extern "C" {
            $(fn $c($($a: $t),+) -> $t;)*
        }
        $(
            #[unsafe(no_mangle)]
            pub extern "C" fn $rok($($a: $t),+) -> $t {
                // SAFETY: libm math functions are pure on their arguments.
                unsafe { $c($($a),+) }
            }
        )*
    };
}

libm! {
    rok_f64_floor = floor(x): f64;
    rok_f64_ceil = ceil(x): f64;
    rok_f64_round = round(x): f64;
    rok_f64_trunc = trunc(x): f64;
    rok_f64_abs = fabs(x): f64;
    rok_f64_cbrt = cbrt(x): f64;
    rok_f64_exp = exp(x): f64;
    rok_f64_exp2 = exp2(x): f64;
    rok_f64_exp_m1 = expm1(x): f64;
    rok_f64_ln = log(x): f64;
    rok_f64_ln_1p = log1p(x): f64;
    rok_f64_log2 = log2(x): f64;
    rok_f64_log10 = log10(x): f64;
    rok_f64_sin = sin(x): f64;
    rok_f64_cos = cos(x): f64;
    rok_f64_tan = tan(x): f64;
    rok_f64_asin = asin(x): f64;
    rok_f64_acos = acos(x): f64;
    rok_f64_atan = atan(x): f64;
    rok_f64_sinh = sinh(x): f64;
    rok_f64_cosh = cosh(x): f64;
    rok_f64_tanh = tanh(x): f64;
    rok_f64_asinh = asinh(x): f64;
    rok_f64_acosh = acosh(x): f64;
    rok_f64_atanh = atanh(x): f64;
    rok_f64_pow = pow(x, y): f64;
    rok_f64_atan2 = atan2(x, y): f64;
    rok_f64_hypot = hypot(x, y): f64;
    rok_f64_copysign = copysign(x, y): f64;
    rok_f64_min = fmin(x, y): f64;
    rok_f64_max = fmax(x, y): f64;
    rok_f64_mul_add = fma(x, y, z): f64;

    rok_f32_floor = floorf(x): f32;
    rok_f32_ceil = ceilf(x): f32;
    rok_f32_round = roundf(x): f32;
    rok_f32_trunc = truncf(x): f32;
    rok_f32_abs = fabsf(x): f32;
    rok_f32_cbrt = cbrtf(x): f32;
    rok_f32_exp = expf(x): f32;
    rok_f32_exp2 = exp2f(x): f32;
    rok_f32_exp_m1 = expm1f(x): f32;
    rok_f32_ln = logf(x): f32;
    rok_f32_ln_1p = log1pf(x): f32;
    rok_f32_log2 = log2f(x): f32;
    rok_f32_log10 = log10f(x): f32;
    rok_f32_sin = sinf(x): f32;
    rok_f32_cos = cosf(x): f32;
    rok_f32_tan = tanf(x): f32;
    rok_f32_asin = asinf(x): f32;
    rok_f32_acos = acosf(x): f32;
    rok_f32_atan = atanf(x): f32;
    rok_f32_sinh = sinhf(x): f32;
    rok_f32_cosh = coshf(x): f32;
    rok_f32_tanh = tanhf(x): f32;
    rok_f32_asinh = asinhf(x): f32;
    rok_f32_acosh = acoshf(x): f32;
    rok_f32_atanh = atanhf(x): f32;
    rok_f32_pow = powf(x, y): f32;
    rok_f32_atan2 = atan2f(x, y): f32;
    rok_f32_hypot = hypotf(x, y): f32;
    rok_f32_copysign = copysignf(x, y): f32;
    rok_f32_min = fminf(x, y): f32;
    rok_f32_max = fmaxf(x, y): f32;
    rok_f32_mul_add = fmaf(x, y, z): f32;
}
