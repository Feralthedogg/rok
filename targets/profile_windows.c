// compiler-rt's profile runtime is compiled for Windows against
// mingw-w64's headers (targets/build.sh); this is what it then needs
// from mingw's own libraries, over the UCRT and rok's startup.

#include <stddef.h>
#include <stdarg.h>

typedef struct _iobuf FILE;

int __stdio_common_vfprintf(unsigned long long, FILE *, const char *, void *,
                            va_list);
int __stdio_common_vsprintf(unsigned long long, char *, size_t, const char *,
                            void *, va_list);
int _crt_atexit(void (*)(void));
void __llvm_profile_initialize(void);

// InstrProfilingRuntime.cpp's registration, which a mingw build would put
// in `.ctors`; rok's startup runs `.CRT$XC*`.
int __llvm_profile_runtime;

static void init(void) { __llvm_profile_initialize(); }

__attribute__((section(".CRT$XCU"), used)) static void (*const init_entry)(void) = init;

int atexit(void (*f)(void)) { return _crt_atexit(f); }

int fprintf(FILE *f, const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  int r = __stdio_common_vfprintf(0, f, fmt, NULL, ap);
  va_end(ap);
  return r;
}

// _CRT_INTERNAL_PRINTF_STANDARD_SNPRINTF_BEHAVIOR: C99's return value.
int snprintf(char *s, size_t n, const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  int r = __stdio_common_vsprintf(2, s, n, fmt, NULL, ap);
  va_end(ap);
  return r < 0 ? -1 : r;
}

// mingw's stack probe for dynamic allocas has MSVC's contract on x86_64
// (`___chkstk_ms`) and i686 (`_alloca`): rok's `__chkstk` does it.
#if defined(__x86_64__)
__asm__(".globl ___chkstk_ms\n___chkstk_ms:\n  jmp __chkstk\n");
#elif defined(__i386__)
__asm__(".globl __alloca\n__alloca:\n  jmp __chkstk\n");
#endif
