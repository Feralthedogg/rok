// The `rokc repl` session host (repl.rs). One process, runtime up
// once, LLVM's ORC JIT linked in (the LLVM-C API; rokc itself never
// links LLVM, 0.2.4). Commands come on the socket rokc passes as stdin:
//
//   `cell <n>\n` + n bytes of LLVM IR: JIT-compile it into the session
//     and run its `rok_repl_cell` once. Later cells link against it.
//   `once <n> <out> <err>\n` + n bytes of LLVM IR (`--replay`): compile
//     and run it in a throwaway child (stdout / stderr into the files
//     `out` / `err`); the session itself never runs anything.
//   `lib <n>\n` + an n-byte path: link a prebuilt dependency's static
//     library into the session (its members load as cells need them);
//     the reply is `ok 0\n` or `err\n`.
//
// A cell's reply is `pid <p>\n` (the process running the cell) and then
// `ok <n>\n<n bytes of the shown value>` or `err\n`. `SIGINT` ends a
// running cell (the session goes on as before it) and is ignored
// between cells. argv[1] is the opt level (`0`..`3`, `s`).
//
// All cells share one JITDylib. A cell that defines a symbol an earlier
// cell defined (a redefined `fn`, `static`, the user `main`, ..) gets it
// renamed `<name>.r<cell>`, and later cells' references to the name are
// renamed to the newest one: a redefinition takes effect from the next
// cell (907) while earlier code keeps what it was linked against.
#include <fcntl.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

#include <llvm-c/Core.h>
#include <llvm-c/Error.h>
#include <llvm-c/IRReader.h>
#include <llvm-c/LLJIT.h>
#include <llvm-c/Orc.h>
#include <llvm-c/Target.h>
#include <llvm-c/Transforms/PassBuilder.h>

void rok_runtime_init(void);

// The cell's shown value (a rok `str`), which the cell sets.
struct {
    const char *ptr;
    size_t len;
} __rok_repl_out;

static LLVMOrcLLJITRef jit;
static LLVMOrcJITDylibRef jd;
static const char *opt_level = "0";
static unsigned cells;

// Symbols the session defines: name → its newest definition's name.
struct sym {
    char *name, *now;
    struct sym *next;
};
static struct sym *syms[4096];

static struct sym **sym_slot(const char *name) {
    unsigned h = 2166136261u;
    for (const char *s = name; *s; s++) h = (h ^ (unsigned char)*s) * 16777619u;
    struct sym **p = &syms[h % (sizeof syms / sizeof *syms)];
    while (*p && strcmp((*p)->name, name)) p = &(*p)->next;
    return p;
}

static const char *sym_now(const char *name) {
    struct sym *s = *sym_slot(name);
    return s ? s->now : NULL;
}

static void sym_set(const char *name, const char *now) {
    struct sym **p = sym_slot(name);
    if (!*p) {
        *p = calloc(1, sizeof **p);
        (*p)->name = strdup(name);
    }
    free((*p)->now);
    (*p)->now = strdup(now);
}

static int report(LLVMErrorRef e) {
    if (!e) return 0;
    char *m = LLVMGetErrorMessage(e);
    fprintf(stderr, "error: %s\n", m);
    LLVMDisposeErrorMessage(m);
    return 1;
}

#if defined(__APPLE__)
#include <mach-o/dyld.h>
#include <mach-o/loader.h>
#include <mach-o/nlist.h>

// A symbol of the host executable by its symbol table, not `dlsym`: a
// thread-local reference wants its TLV descriptor, which `dlsym` does
// not give (it returns this thread's instance).
static void *host_symbol(const char *name) {
    const struct mach_header_64 *mh = (const void *)_dyld_get_image_header(0);
    intptr_t slide = _dyld_get_image_vmaddr_slide(0);
    const struct load_command *lc = (const void *)(mh + 1);
    const struct segment_command_64 *linkedit = NULL;
    const struct symtab_command *st = NULL;
    for (uint32_t i = 0; i < mh->ncmds; i++, lc = (const void *)((const char *)lc + lc->cmdsize)) {
        if (lc->cmd == LC_SEGMENT_64 && !strcmp(((const struct segment_command_64 *)lc)->segname, "__LINKEDIT"))
            linkedit = (const void *)lc;
        if (lc->cmd == LC_SYMTAB) st = (const void *)lc;
    }
    if (!linkedit || !st) return NULL;
    const char *base = (const char *)(linkedit->vmaddr + slide - linkedit->fileoff);
    const struct nlist_64 *nl = (const void *)(base + st->symoff);
    const char *strs = base + st->stroff;
    // Linear scan: runs once per thread-local the session uses.
    for (uint32_t i = 0; i < st->nsyms; i++)
        if (!(nl[i].n_type & N_STAB) && (nl[i].n_type & N_TYPE) == N_SECT &&
            !strcmp(strs + nl[i].n_un.n_strx, name))
            return (void *)(nl[i].n_value + slide);
    return NULL;
}

// The thread-locals `m` uses, defined as their descriptors in the host
// (the process-symbol generator would find them by `dlsym`).
static int define_thread_locals(LLVMModuleRef m) {
    for (LLVMValueRef g = LLVMGetFirstGlobal(m); g; g = LLVMGetNextGlobal(g)) {
        if (!LLVMIsDeclaration(g) || !LLVMIsThreadLocal(g)) continue;
        size_t len;
        const char *n = LLVMGetValueName2(g, &len);
        char mangled[512];
        snprintf(mangled, sizeof mangled, "%c%s", LLVMOrcLLJITGetGlobalPrefix(jit), n);
        if (sym_now(mangled)) continue;
        void *desc = host_symbol(mangled);
        if (!desc) {
            fprintf(stderr, "error: no thread-local `%s` in the session host\n", n);
            return 1;
        }
        LLVMOrcCSymbolMapPair pair = {
            LLVMOrcExecutionSessionIntern(LLVMOrcLLJITGetExecutionSession(jit), mangled),
            {(LLVMOrcExecutorAddress)(uintptr_t)desc, {LLVMJITSymbolGenericFlagsExported, 0}},
        };
        if (report(LLVMOrcJITDylibDefine(jd, LLVMOrcAbsoluteSymbols(&pair, 1)))) return 1;
        sym_set(mangled, mangled);
    }
    return 0;
}
#else
// ELF thread-locals go through the process-symbol generator;
// untested off macOS.
static int define_thread_locals(LLVMModuleRef m) {
    (void)m;
    return 0;
}
#endif

// Give `v` (a definition or a declaration of `m`) its session name.
static void rename_value(LLVMValueRef v) {
    LLVMLinkage l = LLVMGetLinkage(v);
    if (l == LLVMInternalLinkage || l == LLVMPrivateLinkage) return;
    size_t len;
    const char *n = LLVMGetValueName2(v, &len);
    if (!len || !strncmp(n, "llvm.", 5)) return;
    char *name = strdup(n);
    const char *now = sym_now(name);
    if (!LLVMIsDeclaration(v)) {
        if (now) {
            char fresh[1024];
            snprintf(fresh, sizeof fresh, "%s.r%u", name, cells);
            LLVMSetValueName2(v, fresh, strlen(fresh));
            sym_set(name, fresh);
        } else
            sym_set(name, name);
    } else if (now && strcmp(now, name))
        LLVMSetValueName2(v, now, strlen(now));
    free(name);
}

// Parse, rename, compile the cell `ir`; its entry point (NULL: failed,
// reported).
static void (*jit_cell(const char *ir, size_t n))(void) {
    cells++;
    LLVMContextRef ctx = LLVMContextCreate();
    LLVMMemoryBufferRef buf = LLVMCreateMemoryBufferWithMemoryRangeCopy(ir, n, "cell");
    LLVMModuleRef m;
    char *msg = NULL;
    if (LLVMParseIRInContext(ctx, buf, &m, &msg)) {
        fprintf(stderr, "error: cannot read the cell's LLVM IR: %s\n", msg);
        LLVMDisposeMessage(msg);
        LLVMContextDispose(ctx);
        return NULL;
    }
    LLVMSetDataLayout(m, LLVMOrcLLJITGetDataLayoutStr(jit));
    LLVMSetTarget(m, LLVMOrcLLJITGetTripleString(jit));
    if (define_thread_locals(m)) return NULL;
    // Definitions first: a declaration may name a symbol this very
    // module redefines only when it is not here at all.
    for (int defs = 1; defs >= 0; defs--) {
        for (LLVMValueRef f = LLVMGetFirstFunction(m); f; f = LLVMGetNextFunction(f))
            if (!LLVMIsDeclaration(f) == defs) rename_value(f);
        for (LLVMValueRef g = LLVMGetFirstGlobal(m); g; g = LLVMGetNextGlobal(g))
            if (!LLVMIsDeclaration(g) == defs) rename_value(g);
    }
    if (strcmp(opt_level, "0")) {
        char passes[32];
        snprintf(passes, sizeof passes, "default<O%s>", opt_level);
        LLVMPassBuilderOptionsRef po = LLVMCreatePassBuilderOptions();
        LLVMErrorRef e = LLVMRunPasses(m, passes, NULL, po);
        LLVMDisposePassBuilderOptions(po);
        if (report(e)) return NULL;
    }
    LLVMOrcThreadSafeContextRef ts = LLVMOrcCreateNewThreadSafeContextFromLLVMContext(ctx);
    LLVMOrcThreadSafeModuleRef tsm = LLVMOrcCreateNewThreadSafeModule(m, ts);
    LLVMOrcDisposeThreadSafeContext(ts);
    if (report(LLVMOrcLLJITAddLLVMIRModule(jit, jd, tsm))) return NULL;
    LLVMOrcExecutorAddress entry = 0;
    if (report(LLVMOrcLLJITLookup(jit, &entry, sym_now("rok_repl_cell")))) return NULL;
    return (void (*)(void))(uintptr_t)entry;
}

static void start_jit(void) {
    LLVMInitializeNativeTarget();
    LLVMInitializeNativeAsmPrinter();
    char *triple = LLVMGetDefaultTargetTriple(), *err = NULL;
    LLVMTargetRef target;
    if (LLVMGetTargetFromTriple(triple, &target, &err)) {
        fprintf(stderr, "error: %s\n", err);
        exit(1);
    }
    LLVMCodeGenOptLevel level = !strcmp(opt_level, "0")   ? LLVMCodeGenLevelNone
                                : !strcmp(opt_level, "3") ? LLVMCodeGenLevelAggressive
                                                          : LLVMCodeGenLevelDefault;
    char *cpu = LLVMGetHostCPUName(), *features = LLVMGetHostCPUFeatures();
    LLVMTargetMachineRef tm = LLVMCreateTargetMachine(target, triple, cpu, features, level,
                                                      LLVMRelocDefault, LLVMCodeModelJITDefault);
    LLVMDisposeMessage(triple);
    LLVMDisposeMessage(cpu);
    LLVMDisposeMessage(features);
    LLVMOrcLLJITBuilderRef b = LLVMOrcCreateLLJITBuilder();
    LLVMOrcLLJITBuilderSetJITTargetMachineBuilder(b, LLVMOrcJITTargetMachineBuilderCreateFromTargetMachine(tm));
    if (report(LLVMOrcCreateLLJIT(&jit, b))) exit(1);
    jd = LLVMOrcLLJITGetMainJITDylib(jit);
    // The runtime (linked in whole), libc, and `__rok_repl_out`.
    LLVMOrcDefinitionGeneratorRef gen;
    if (report(LLVMOrcCreateDynamicLibrarySearchGeneratorForProcess(&gen, LLVMOrcLLJITGetGlobalPrefix(jit), NULL, NULL)))
        exit(1);
    LLVMOrcJITDylibAddGenerator(jd, gen);
}

// A command line: `<word> <n> [<out> <err>]`.
static int read_command(int ctl, char *line, size_t cap) {
    size_t n = 0;
    char c;
    while (read(ctl, &c, 1) == 1 && c != '\n')
        if (n < cap - 1) line[n++] = c;
    line[n] = 0;
    return n > 0;
}

static char *read_ir(int ctl, size_t n) {
    char *ir = malloc(n + 1);
    size_t got = 0;
    while (ir && got < n) {
        ssize_t r = read(ctl, ir + got, n - got);
        if (r <= 0) {
            free(ir);
            return NULL;
        }
        got += (size_t)r;
    }
    return ir;
}

// `--replay`: run `ir` in a child with its output in `out` / `err`.
static void run_once(int ctl, const char *ir, size_t n, const char *out, const char *err) {
    pid_t child = fork();
    if (child == 0) {
        int o = open(out, O_WRONLY | O_CREAT | O_TRUNC, 0600);
        int e = open(err, O_WRONLY | O_CREAT | O_TRUNC, 0600);
        if (o < 0 || e < 0) _exit(1);
        dup2(o, 1);
        dup2(e, 2);
        signal(SIGINT, SIG_DFL);
        void (*cell)(void) = jit_cell(ir, n);
        if (cell) cell();
        fflush(stdout);
        fflush(stderr);
        _exit(cell ? 0 : 1);
    }
    dprintf(ctl, "pid %d\n", (int)child);
    int st = 1;
    if (child > 0) waitpid(child, &st, 0);
    dprintf(ctl, st == 0 ? "ok 0\n" : "err\n");
}

int main(int argc, char **argv) {
    if (argc > 1) opt_level = argv[1];
    int ctl = dup(0);
    int nul = open("/dev/null", O_RDONLY);
    dup2(nul, 0);  // the cells' stdin
    close(nul);
    rok_runtime_init();
    start_jit();
    signal(SIGINT, SIG_IGN);
    for (;;) {
        char line[8192], out[4096] = "", err[4096] = "", c;
        size_t n = 0;
        if (!read_command(ctl, line, sizeof line)) return 0;
        char *ir = NULL;
        if (sscanf(line, "lib %zu", &n) == 1) {
            char *path = read_ir(ctl, n);
            if (!path) return 1;
            path[n] = 0;
            LLVMOrcDefinitionGeneratorRef lib;
            LLVMOrcObjectLayerRef layer = LLVMOrcLLJITGetObjLinkingLayer(jit);
            int bad = report(LLVMOrcCreateStaticLibrarySearchGeneratorForPath(&lib, layer, path));
            if (!bad) LLVMOrcJITDylibAddGenerator(jd, lib);
            free(path);
            dprintf(ctl, bad ? "err\n" : "ok 0\n");
            continue;
        }
        if (sscanf(line, "cell %zu", &n) == 1 || sscanf(line, "once %zu %4095s %4095s", &n, out, err) == 3)
            ir = read_ir(ctl, n);
        if (!ir) return 1;
        fflush(stdout);
        if (line[0] == 'o') {
            run_once(ctl, ir, n, out, err);
            free(ir);
            continue;
        }
        // A copy of the session from before the cell. When the cell's
        // process dies (panic, signal, exit, a cell that does not
        // compile) the copy carries on as the session; otherwise it is
        // told to go. The JIT has no threads of its own (in-place
        // compilation), so the copy's is whole.
        // Threads other than this one are not in the copy.
        int verdict[2];
        if (pipe(verdict) != 0) return 1;
        pid_t snap = fork();
        if (snap == 0) {
            close(verdict[1]);
            ssize_t r;
            while ((r = read(verdict[0], &c, 1)) < 0) {}
            if (r == 1) _exit(0);
            close(verdict[0]);
            free(ir);
            dprintf(ctl, "err\n");
            continue;
        }
        close(verdict[0]);
        dprintf(ctl, "pid %d\n", (int)getpid());
        signal(SIGINT, SIG_DFL);
        void (*cell)(void) = jit_cell(ir, n);
        free(ir);
        if (!cell) _exit(1);  // the copy, from before the cell, goes on
        __rok_repl_out.len = 0;
        cell();
        signal(SIGINT, SIG_IGN);
        fflush(stdout);
        if (write(verdict[1], "", 1) != 1) {}
        close(verdict[1]);
        if (snap > 0) waitpid(snap, NULL, 0);
        dprintf(ctl, "ok %zu\n", __rok_repl_out.len);
        if (write(ctl, __rok_repl_out.ptr, __rok_repl_out.len) < 0) return 1;
    }
}
