// The `rokc repl` session host (repl.rs). One process, runtime up
// once, LLVM's ORC JIT linked in (the LLVM-C API; rokc itself never
// links LLVM, 0.2.4). Commands come on the socket rokc passes as stdin:
//
//   `cell <n>\n` + n bytes of LLVM IR: JIT-compile it into the session
//     and run its `rok_repl_cell` once. Later cells link against it.
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
//
// Built with `ROK_NATIVE_JIT` (the native backend's cells, `-O0`), the
// host links no LLVM: a cell is a Mach-O object rokc compiled, and the
// host maps, links and runs it itself (`jit_cell` below); `lib` loads
// every member of the archive the same way.
#include <fcntl.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

#ifndef ROK_NATIVE_JIT
#include <llvm-c/Core.h>
#include <llvm-c/Error.h>
#include <llvm-c/IRReader.h>
#include <llvm-c/LLJIT.h>
#include <llvm-c/Orc.h>
#include <llvm-c/Target.h>
#include <llvm-c/Transforms/PassBuilder.h>
#endif

void rok_runtime_init(void);
int rok_stdio_flush(void);

// The cell's shown value (a rok `str`), which the cell sets.
struct {
    const char *ptr;
    size_t len;
} __rok_repl_out;

#ifndef ROK_NATIVE_JIT
static LLVMOrcLLJITRef jit;
static LLVMOrcJITDylibRef jd;
#endif
static const char *opt_level = "0";
static unsigned cells;

// Symbols the session defines: name → its newest definition's name
// (and, native, a definition's address under its own name).
struct sym {
    char *name, *now;
    void *addr;
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
#endif

#ifndef ROK_NATIVE_JIT
static int report(LLVMErrorRef e) {
    if (!e) return 0;
    char *m = LLVMGetErrorMessage(e);
    fprintf(stderr, "error: %s\n", m);
    LLVMDisposeErrorMessage(m);
    return 1;
}

#if defined(__APPLE__)
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
    // SelectionDAG only, as rokc's clang -fno-global-isel: mixing it with
    // GlobalISel splits aggregate arguments' stack layout.
    LLVMSetTargetMachineGlobalISel(tm, 0);
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

// A prebuilt dependency's archive: its members load as cells need them.
static int link_lib(const char *path) {
    LLVMOrcDefinitionGeneratorRef lib;
    LLVMOrcObjectLayerRef layer = LLVMOrcLLJITGetObjLinkingLayer(jit);
    int bad = report(LLVMOrcCreateStaticLibrarySearchGeneratorForPath(&lib, layer, path));
    if (!bad) LLVMOrcJITDylibAddGenerator(jd, lib);
    return bad;
}
#else
// The native JIT: Mach-O arm64 objects (MH_OBJECT) mapped into
// executable memory, linked against the session and the host.
#include <dlfcn.h>
#include <mach-o/reloc.h>
#include <libkern/OSCacheControl.h>
#include <pthread.h>
#include <sys/mman.h>

static void *sym_addr(const char *now) {
    struct sym *s = *sym_slot(now);
    return s ? s->addr : NULL;
}

// A definition of `name` at `addr`: renamed `<name>.r<cell>` when an
// earlier cell has one (later cells use the newest).
static void define(const char *name, void *addr) {
    char fresh[1024];
    const char *as = name;
    if (sym_now(name)) {
        snprintf(fresh, sizeof fresh, "%s.r%u", name, cells);
        as = fresh;
    }
    sym_set(name, as);
    if (as != name) sym_set(as, as);
    (*sym_slot(as))->addr = addr;
}

// An undefined symbol: the session's newest definition, else the host's
// (a thread-local: its descriptor).
static void *resolve(const char *name, int tlv) {
    const char *now = sym_now(name);
    void *a = now ? sym_addr(now) : NULL;
    if (a) return a;
    if (tlv) return host_symbol(name);
    a = dlsym(RTLD_DEFAULT, name + 1);
    return a ? a : host_symbol(name);
}

enum { R_UNSIGNED = 0, R_BRANCH26 = 2, R_PAGE21 = 3, R_PAGEOFF12 = 4, R_GOT21 = 5, R_GOT12 = 6,
       R_TLV21 = 8, R_TLV12 = 9, R_ADDEND = 10 };

// An object mapped, its symbols defined, not yet linked.
struct obj {
    const unsigned char *buf;
    const char *what;
    const struct section_64 *sects;
    uint32_t nsects, nsyms;
    const struct nlist_64 *nl;
    const char *strs;
    // Code (executable, `MAP_JIT`) and data (writable) mappings; GOT
    // slots go after the data, branch stubs after the code.
    char *code, *data, **base, **addr;
    size_t code_cap, data_cap, stubs, slots;
    void *entry;
};

// Map `buf` and define its exported symbols (0: failed, reported).
static int map_object(struct obj *o, const unsigned char *buf, size_t n, const char *what) {
    memset(o, 0, sizeof *o);
    o->buf = buf;
    o->what = what;
    const struct mach_header_64 *mh = (const void *)buf;
    if (n < sizeof *mh || mh->magic != MH_MAGIC_64 || mh->cputype != CPU_TYPE_ARM64) {
        fprintf(stderr, "error: %s: not an arm64 Mach-O object\n", what);
        return 0;
    }
    const struct symtab_command *st = NULL;
    const struct load_command *lc = (const void *)(mh + 1);
    for (uint32_t i = 0; i < mh->ncmds; i++, lc = (const void *)((const char *)lc + lc->cmdsize)) {
        if (lc->cmd == LC_SEGMENT_64) {
            o->sects = (const void *)((const struct segment_command_64 *)lc + 1);
            o->nsects = ((const struct segment_command_64 *)lc)->nsects;
        }
        if (lc->cmd == LC_SYMTAB) st = (const void *)lc;
    }
    // What runs is mapped: not debug info, unwind tables or the like.
    size_t code = 0, data = 0, nrel = 0, *at = calloc(o->nsects + 1, sizeof *at);
    int *is_code = calloc(o->nsects + 1, sizeof *is_code);
    for (uint32_t k = 0; k < o->nsects; k++) {
        const struct section_64 *s = &o->sects[k];
        if ((s->flags & S_ATTR_DEBUG) || !strcmp(s->segname, "__LD") || !strcmp(s->sectname, "__eh_frame"))
            continue;
        is_code[k] = (s->flags & (S_ATTR_PURE_INSTRUCTIONS | S_ATTR_SOME_INSTRUCTIONS)) != 0;
        size_t *end = is_code[k] ? &code : &data, a = (size_t)1 << s->align;
        *end = (*end + a - 1) & ~(a - 1);
        at[k] = *end + 1;
        *end += s->size;
        nrel += s->nreloc;
    }
    // Branch stubs (16 bytes) and GOT slots (8): one per relocation at
    // most.
    o->stubs = code = (code + 15) & ~(size_t)15;
    o->slots = data = (data + 15) & ~(size_t)15;
    o->code_cap = code + 16 * nrel + 16;
    o->data_cap = data + 8 * nrel + 16;
    // Both near each other: `adrp` reaches 4 GiB.
    o->data = mmap(NULL, o->data_cap, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON, -1, 0);
    o->code = o->data == MAP_FAILED ? MAP_FAILED
                                    : mmap(o->data + ((o->data_cap + 0x3fff) & ~(size_t)0x3fff), o->code_cap,
                                           PROT_READ | PROT_WRITE | PROT_EXEC, MAP_PRIVATE | MAP_ANON | MAP_JIT, -1, 0);
    if (o->code == MAP_FAILED) {
        fprintf(stderr, "error: %s: cannot map executable memory\n", what);
        free(at);
        free(is_code);
        return 0;
    }
    o->base = calloc(o->nsects + 1, sizeof *o->base);
    pthread_jit_write_protect_np(0);
    for (uint32_t k = 0; k < o->nsects; k++) {
        if (!at[k]) continue;
        o->base[k] = (is_code[k] ? o->code : o->data) + at[k] - 1;
        if ((o->sects[k].flags & SECTION_TYPE) != S_ZEROFILL)
            memcpy(o->base[k], buf + o->sects[k].offset, o->sects[k].size);
    }
    pthread_jit_write_protect_np(1);
    free(at);
    free(is_code);
    o->nl = st ? (const void *)(buf + st->symoff) : NULL;
    o->strs = st ? (const char *)buf + st->stroff : "";
    o->nsyms = st ? st->nsyms : 0;
    o->addr = calloc(o->nsyms + 1, sizeof *o->addr);
    for (uint32_t i = 0; i < o->nsyms; i++) {
        const struct nlist_64 *s = &o->nl[i];
        if ((s->n_type & N_STAB) || (s->n_type & N_TYPE) != N_SECT) continue;
        uint32_t k = s->n_sect - 1;
        if (k >= o->nsects || !o->base[k]) continue;
        o->addr[i] = o->base[k] + (s->n_value - o->sects[k].addr);
        const char *name = o->strs + s->n_un.n_strx;
        if (s->n_type & N_EXT) define(name, o->addr[i]);
        if (!strcmp(name, "_rok_repl_cell")) o->entry = o->addr[i];
    }
    return 1;
}

// Apply `o`'s relocations (0: failed, reported).
static int link_object(struct obj *o) {
    char **got = calloc(o->nsyms + 1, sizeof *got), **stub = calloc(o->nsyms + 1, sizeof *stub);
    int ok = 1;
    pthread_jit_write_protect_np(0);
    for (uint32_t k = 0; k < o->nsects && ok; k++) {
        if (!o->base[k]) continue;
        const struct relocation_info *rel = (const void *)(o->buf + o->sects[k].reloff);
        int64_t addend = 0;
        for (uint32_t r = 0; r < o->sects[k].nreloc && ok; r++, addend = 0) {
            struct relocation_info ri = rel[r];
            if (ri.r_type == R_ADDEND) {
                addend = ((int64_t)ri.r_symbolnum << 40) >> 40;
                ri = rel[++r];
            }
            char *p = o->base[k] + ri.r_address;
            uint32_t i = ri.r_symbolnum, ins;
            memcpy(&ins, p, 4);
            uint64_t s = 0;
            int tlv = ri.r_type == R_TLV21 || ri.r_type == R_TLV12;
            if (ri.r_extern) {
                s = (uint64_t)(uintptr_t)o->addr[i];
                if (!s) {
                    const char *name = o->strs + o->nl[i].n_un.n_strx;
                    s = (uint64_t)(uintptr_t)resolve(name, tlv);
                    if (!s) {
                        fprintf(stderr, "error: %s: undefined symbol `%s`\n", o->what, name + 1);
                        ok = 0;
                        break;
                    }
                }
            } else if (i >= 1 && i <= o->nsects && o->base[i - 1]) {
                // Section-relative: the bytes hold the object address.
                s = (uint64_t)(uintptr_t)o->base[i - 1] - o->sects[i - 1].addr;
            }
            uint64_t target = s + (uint64_t)addend;
            switch (ri.r_type) {
            case R_UNSIGNED:
                if (ri.r_length == 3) {
                    uint64_t v;
                    memcpy(&v, p, 8);
                    v += target;
                    memcpy(p, &v, 8);
                } else {
                    uint32_t v;
                    memcpy(&v, p, 4);
                    v += (uint32_t)target;
                    memcpy(p, &v, 4);
                }
                break;
            case R_BRANCH26: {
                int64_t d = (int64_t)target - (int64_t)(uintptr_t)p;
                if (d >= (1 << 27) || d < -(1 << 27)) {
                    // Far (the host's code): through a stub.
                    char *t = ri.r_extern ? stub[i] : NULL;
                    if (!t) {
                        t = o->code + o->stubs;
                        o->stubs += 16;
                        uint32_t code[2] = {0x58000050, 0xd61f0200}; // ldr x16, #8; br x16
                        memcpy(t, code, 8);
                        memcpy(t + 8, &target, 8);
                        if (ri.r_extern) stub[i] = t;
                    }
                    d = t - p;
                }
                ins = (ins & 0xfc000000) | ((uint32_t)(d >> 2) & 0x03ffffff);
                memcpy(p, &ins, 4);
                break;
            }
            case R_GOT21: case R_GOT12: case R_TLV21: case R_TLV12: case R_PAGE21: case R_PAGEOFF12: {
                if (ri.r_type != R_PAGE21 && ri.r_type != R_PAGEOFF12) {
                    // A slot holding the address (a thread-local's: its
                    // descriptor's).
                    char *g = ri.r_extern ? got[i] : NULL;
                    if (!g) {
                        g = o->data + o->slots;
                        o->slots += 8;
                        memcpy(g, &target, 8);
                        if (ri.r_extern) got[i] = g;
                    }
                    target = (uint64_t)(uintptr_t)g;
                }
                if (ri.r_type == R_PAGE21 || ri.r_type == R_GOT21 || ri.r_type == R_TLV21) {
                    int64_t pages = (int64_t)(target >> 12) - (int64_t)((uintptr_t)p >> 12);
                    if (pages >= (1 << 20) || pages < -(1 << 20)) {
                        fprintf(stderr, "error: %s: a page reference out of range\n", o->what);
                        ok = 0;
                        break;
                    }
                    ins = (ins & 0x9f00001f) | (((uint32_t)pages & 3) << 29) |
                          ((((uint32_t)pages >> 2) & 0x7ffff) << 5);
                } else {
                    uint32_t lo = (uint32_t)(target & 0xfff);
                    // A load / store scales its offset by the access size.
                    if ((ins & 0x3b000000) == 0x39000000) {
                        uint32_t scale = ins >> 30;
                        if ((ins & 0x04800000) == 0x04800000) scale = 4; // 128-bit vector
                        lo >>= scale;
                    }
                    ins = (ins & 0xffc003ff) | ((lo & 0xfff) << 10);
                }
                memcpy(p, &ins, 4);
                break;
            }
            default:
                fprintf(stderr, "error: %s: relocation type %u is not supported\n", o->what, ri.r_type);
                ok = 0;
            }
        }
    }
    pthread_jit_write_protect_np(1);
    sys_icache_invalidate(o->code, o->code_cap);
    free(got);
    free(stub);
    free(o->base);
    free(o->addr);
    return ok;
}

// Map and link the cell; its entry point (NULL: failed, reported).
static void (*jit_cell(const char *obj, size_t n))(void) {
    cells++;
    struct obj o;
    if (!map_object(&o, (const unsigned char *)obj, n, "cell") || !link_object(&o) || !o.entry)
        return NULL;
    return (void (*)(void))o.entry;
}

static void start_jit(void) {}

// A prebuilt dependency's archive: every member, now (mapped first, so
// they refer to each other).
static int link_lib(const char *path) {
    int fd = open(path, O_RDONLY);
    if (fd < 0) return 1;
    off_t size = lseek(fd, 0, SEEK_END);
    char *a = mmap(NULL, (size_t)size, PROT_READ, MAP_PRIVATE, fd, 0);
    close(fd);
    if (a == MAP_FAILED || size < 8 || memcmp(a, "!<arch>\n", 8)) return 1;
    struct obj objs[256];
    int n = 0;
    cells++;
    for (size_t off = 8; off + 60 <= (size_t)size && n < 256;) {
        const char *h = a + off;
        size_t len = strtoul(h + 48, NULL, 10), skip = 0;
        if (!memcmp(h, "#1/", 3)) skip = strtoul(h + 3, NULL, 10);
        const char *name = skip ? h + 60 : h;
        const unsigned char *body = (const unsigned char *)h + 60 + skip;
        if (strncmp(name, "__.SYMDEF", 9) && len > skip) {
            if (!map_object(&objs[n], body, len - skip, path)) return 1;
            n++;
        }
        off += 60 + len;
        off += off & 1;
    }
    for (int i = 0; i < n; i++)
        if (!link_object(&objs[i])) return 1;
    return 0;
}
#endif

// A command line: `<word> <n>`.
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
        char line[8192], c;
        size_t n = 0;
        if (!read_command(ctl, line, sizeof line)) return 0;
        char *ir = NULL;
        if (sscanf(line, "lib %zu", &n) == 1) {
            char *path = read_ir(ctl, n);
            if (!path) return 1;
            path[n] = 0;
            int bad = link_lib(path);
            free(path);
            dprintf(ctl, bad ? "err\n" : "ok 0\n");
            continue;
        }
        if (sscanf(line, "cell %zu", &n) == 1) ir = read_ir(ctl, n);
        if (!ir) return 1;
        rok_stdio_flush();
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
        rok_stdio_flush();
        if (write(verdict[1], "", 1) != 1) {}
        close(verdict[1]);
        if (snap > 0) waitpid(snap, NULL, 0);
        dprintf(ctl, "ok %zu\n", __rok_repl_out.len);
        if (write(ctl, __rok_repl_out.ptr, __rok_repl_out.len) < 0) return 1;
    }
}
