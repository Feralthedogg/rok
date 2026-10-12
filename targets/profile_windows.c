// compiler-rt's profile runtime is compiled for Windows against
// mingw-w64's headers (targets/build.sh); this is what it then needs
// from mingw's own libraries, over the UCRT and rok's startup.

// fprintf and snprintf come from rok's startup (its selectany copies).

int _crt_atexit(void (*)(void));
void __llvm_profile_initialize(void);

// InstrProfilingRuntime.cpp's registration, which a mingw build would put
// in `.ctors`; rok's startup runs `.CRT$XC*`.
int __llvm_profile_runtime;

static void init(void) { __llvm_profile_initialize(); }

__attribute__((section(".CRT$XCU"), used)) static void (*const init_entry)(void) = init;

int atexit(void (*f)(void)) { return _crt_atexit(f); }

// mingw's stack probe for dynamic allocas has MSVC's contract on x86_64
// (`___chkstk_ms`) and i686 (`_alloca`): rok's `__chkstk` does it.
#if defined(__x86_64__)
__asm__(".globl ___chkstk_ms\n___chkstk_ms:\n  jmp __chkstk\n");
#elif defined(__i386__)
__asm__(".globl __alloca\n__alloca:\n  jmp __chkstk\n");
#endif
