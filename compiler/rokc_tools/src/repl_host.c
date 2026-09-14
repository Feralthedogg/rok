// The `rokc repl` session host (repl.rs). One process, runtime up
// once; rokc compiles each cell to an object of the host's format
// (Mach-O on Apple platforms, else ELF; arm64 / x86_64; the native
// backend at `-O0`, LLVM above) and the host maps, links and runs it
// itself (`jit_cell`). Commands come on the socket rokc passes as stdin:
//
//   `cell <n>\n` + n bytes of object: link it into the session and run
//     its `rok_repl_cell` once. Later cells link against it.
//   `lib <n>\n` + an n-byte path: link every member of a prebuilt
//     dependency's static library into the session; the reply is
//     `ok 0\n` or `err\n`.
//
// A cell's reply is `pid <p>\n` (the process running the cell) and then
// `ok <n>\n<n bytes of the shown value>` or `err\n`. `SIGINT` ends a
// running cell (the session goes on as before it) and is ignored
// between cells.
//
// A cell that defines a symbol an earlier cell defined (a redefined
// `fn`, `static`, the user `main`, ..) gets it renamed `<name>.r<cell>`,
// and later cells' references to the name resolve to the newest one: a
// redefinition takes effect from the next cell (907) while earlier code
// keeps what it was linked against.
//
// The loader is one linker over generic sections, symbols and
// relocation kinds (`struct obj`, `fix`); a format reader (`map_object`,
// `link_object`) turns Mach-O or ELF into them. Thread-locals are the
// host's: a Mach-O cell reaches one through its TLV descriptor, an ELF
// cell (initial exec) through its thread-pointer offset.
#define _GNU_SOURCE
#include <dlfcn.h>
#include <fcntl.h>
#include <pthread.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/wait.h>
#include <unistd.h>

#if !defined(__aarch64__) && !defined(__x86_64__)
#error "the REPL host loads arm64 and x86_64 objects only"
#endif

void rok_runtime_init(void);
int rok_stdio_flush(void);

// The cell's shown value (a rok `str`), which the cell sets.
struct {
    const char *ptr;
    size_t len;
} __rok_repl_out;

static unsigned cells;

// Symbols the session defines: name → its newest definition's name
// (and a definition's address under its own name).
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

// Executable memory: Apple arm64 toggles a `MAP_JIT` mapping between
// writable and executable per thread; elsewhere it is mapped RWX.
#if defined(__APPLE__) && defined(__aarch64__)
#include <libkern/OSCacheControl.h>
#define MAP_CODE MAP_JIT
#define jit_writable(on) pthread_jit_write_protect_np(!(on))
#define flush_code(p, n) sys_icache_invalidate(p, n)
#else
#define MAP_CODE 0
#define jit_writable(on) ((void)0)
// x86_64 keeps instruction fetch coherent; arm64 cleans the data cache
// and invalidates the instruction cache by line (no libgcc here for
// `__clear_cache`).
static void flush_code(char *p, size_t n) {
#if defined(__aarch64__)
    uint64_t ctr;
    __asm__ volatile("mrs %0, ctr_el0" : "=r"(ctr));
    uintptr_t d = (uintptr_t)4 << ((ctr >> 16) & 15), i = (uintptr_t)4 << (ctr & 15), end = (uintptr_t)p + n;
    for (uintptr_t a = (uintptr_t)p & ~(d - 1); a < end; a += d) __asm__ volatile("dc cvau, %0" ::"r"(a) : "memory");
    __asm__ volatile("dsb ish" ::: "memory");
    for (uintptr_t a = (uintptr_t)p & ~(i - 1); a < end; a += i) __asm__ volatile("ic ivau, %0" ::"r"(a) : "memory");
    __asm__ volatile("dsb ish\n\tisb" ::: "memory");
#else
    (void)p;
    (void)n;
#endif
}
#endif

#if defined(__APPLE__)
#include <mach-o/dyld.h>
#include <mach-o/loader.h>
#include <mach-o/nlist.h>
#include <mach-o/arm64/reloc.h>
#include <mach-o/reloc.h>
#include <mach-o/x86_64/reloc.h>

// C names carry a leading `_`.
#define SYM_PREFIX 1

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

// A thread-local's value for a cell: its TLV descriptor.
static void *host_tls(const char *name) { return host_symbol(name); }
#else
#include <elf.h>

#define SYM_PREFIX 0

static void *thread_pointer(void) {
    void *tp;
#if defined(__x86_64__)
    __asm__("mov %%fs:0, %0" : "=r"(tp));
#else
    __asm__("mrs %0, tpidr_el0" : "=r"(tp));
#endif
    return tp;
}

// A thread-local's value for a cell: its offset from the thread
// pointer, the same in every thread (the host's TLS is static). `dlsym`
// gives this thread's instance (the host exports its symbols).
static void *host_tls(const char *name) {
    char *a = dlsym(RTLD_DEFAULT, name);
    return a ? (void *)(a - (char *)thread_pointer()) : NULL;
}

static void *host_symbol(const char *name) { return dlsym(RTLD_DEFAULT, name); }
#endif

// An undefined symbol: the session's newest definition, else the
// host's (a thread-local: what `host_tls` gives).
static void *resolve(const char *name, int tls) {
    const char *now = sym_now(name);
    void *a = now ? sym_addr(now) : NULL;
    if (a) return a;
    if (tls) return host_tls(name);
    a = dlsym(RTLD_DEFAULT, name + SYM_PREFIX);
    return a ? a : host_symbol(name);
}

// Relocation kinds, by what they compute (S symbol, A addend, P the
// place, G a slot holding S, T a slot holding the thread-local's value).
enum kind {
    K_ABS64,      // S + A, 64 bits
    K_ABS32,      // S + A, 32 bits
    K_PC32,       // S + A - P, 32 bits
    K_CALL32,     // S + A - P, x86_64 `call` / `jmp`: far through a stub
    K_GOT_PC32,   // G + A - P
    K_TLS_PC32,   // T + A - P
    K_B26,        // arm64 `b` / `bl` to S + A: far through a stub
    K_PAGE21,     // arm64 `adrp` of S + A
    K_LO12,       // arm64 low 12 bits of S + A (scaled for a load / store)
    K_GOT_PAGE21, // ... of G + A
    K_GOT_LO12,
    K_TLS_PAGE21, // ... of T + A
    K_TLS_LO12,
};

// An object mapped, its symbols defined, not yet linked.
struct obj {
    const unsigned char *buf;
    const char *what;
    uint32_t nsects, nsyms;
    // Each section's mapped address (NULL: not mapped) and its address
    // in the object.
    char **base;
    uint64_t *at;
    // Each symbol's address (NULL: undefined here), and its GOT slot and
    // stub once made.
    char **addr, **got, **stub;
    // Code (executable) and data (writable) mappings; GOT slots go after
    // the data, branch stubs after the code.
    char *code, *data;
    size_t code_cap, data_cap, stubs, slots;
    void *entry;
};

// Section `k` of what is mapped: `size` bytes aligned to `align`, code
// or data, copied from `src` (NULL: zero).
struct place {
    uint64_t size, align;
    int code;
    const void *src;
};

// Map the sections (`p[k].size` 0 and `src` NULL: not mapped), with room
// for a stub and a slot per relocation (`nrel`).
static int map_sections(struct obj *o, const struct place *p, size_t nrel) {
    size_t code = 0, data = 0, *off = calloc(o->nsects + 1, sizeof *off);
    for (uint32_t k = 0; k < o->nsects; k++) {
        if (!p[k].align) continue;
        size_t *end = p[k].code ? &code : &data;
        *end = (*end + p[k].align - 1) & ~(size_t)(p[k].align - 1);
        off[k] = *end + 1;
        *end += p[k].size;
    }
    o->stubs = code = (code + 15) & ~(size_t)15;
    o->slots = data = (data + 15) & ~(size_t)15;
    o->code_cap = code + 16 * nrel + 16;
    o->data_cap = data + 8 * nrel + 16;
    // Both near each other and near the host (a cell may address the
    // runtime's data directly): `adrp` reaches 4 GiB, a rip-relative
    // 2 GiB. A hint only: elsewhere when taken, and then a reference
    // too far is reported.
    static char *near;
    if (!near) near = (char *)(((uintptr_t)&cells + ((size_t)1 << 29)) & ~(uintptr_t)0xffff);
    o->data = mmap(near, o->data_cap, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON, -1, 0);
    if (o->data != MAP_FAILED) near = o->data + ((o->data_cap + o->code_cap + 0x7fff) & ~(size_t)0x3fff);
    o->code = o->data == MAP_FAILED ? MAP_FAILED
                                    : mmap(o->data + ((o->data_cap + 0x3fff) & ~(size_t)0x3fff), o->code_cap,
                                           PROT_READ | PROT_WRITE | PROT_EXEC, MAP_PRIVATE | MAP_ANON | MAP_CODE, -1, 0);
    if (o->code == MAP_FAILED) {
        fprintf(stderr, "error: %s: cannot map executable memory\n", o->what);
        free(off);
        return 0;
    }
    o->base = calloc(o->nsects + 1, sizeof *o->base);
    jit_writable(1);
    for (uint32_t k = 0; k < o->nsects; k++) {
        if (!off[k]) continue;
        o->base[k] = (p[k].code ? o->code : o->data) + off[k] - 1;
        if (p[k].src) memcpy(o->base[k], p[k].src, p[k].size);
    }
    jit_writable(0);
    free(off);
    return 1;
}

static void alloc_syms(struct obj *o, uint32_t n) {
    o->nsyms = n;
    o->addr = calloc(n + 1, sizeof *o->addr);
    o->got = calloc(n + 1, sizeof *o->got);
    o->stub = calloc(n + 1, sizeof *o->stub);
}

// Symbol `i` defined at `addr`; `global`: the session's too.
static void def_sym(struct obj *o, uint32_t i, const char *name, char *addr, int global) {
    o->addr[i] = addr;
    if (global) define(name, addr);
    if (!strcmp(name + SYM_PREFIX, "rok_repl_cell")) o->entry = addr;
}

// The address of symbol `i` (`name`), defined here or resolved; 0:
// undefined (reported).
static uint64_t sym_value(struct obj *o, uint32_t i, const char *name, int tls) {
    if (o->addr[i] && !tls) return (uint64_t)(uintptr_t)o->addr[i];
    void *a = resolve(name, tls);
    if (!a) fprintf(stderr, "error: %s: undefined symbol `%s`\n", o->what, name + SYM_PREFIX);
    return (uint64_t)(uintptr_t)a;
}

static char *slot(struct obj *o, int64_t sym, uint64_t value) {
    char *g = sym >= 0 ? o->got[sym] : NULL;
    if (!g) {
        g = o->data + o->slots;
        o->slots += 8;
        memcpy(g, &value, 8);
        if (sym >= 0) o->got[sym] = g;
    }
    return g;
}

static char *stub(struct obj *o, int64_t sym, uint64_t target) {
    char *t = sym >= 0 ? o->stub[sym] : NULL;
    if (!t) {
        t = o->code + o->stubs;
        o->stubs += 16;
#if defined(__x86_64__)
        // jmp *2(%rip): the address at +8, after the 6-byte jmp and 2 pad
        static const unsigned char jmp[8] = {0xff, 0x25, 2, 0, 0, 0, 0x90, 0x90};
        memcpy(t, jmp, 8);
#else
        static const uint32_t br[2] = {0x58000050, 0xd61f0200}; // ldr x16, #8; br x16
        memcpy(t, br, 8);
#endif
        memcpy(t + 8, &target, 8);
        if (sym >= 0) o->stub[sym] = t;
    }
    return t;
}

// Apply one relocation at `p`: symbol index `sym` (-1: none) with value
// `s`, addend `a` (0: failed, reported).
static int fix(struct obj *o, char *p, enum kind k, int64_t sym, uint64_t s, int64_t a) {
    uint64_t pc = (uint64_t)(uintptr_t)p;
    switch (k) {
    case K_GOT_PC32: case K_GOT_PAGE21: case K_GOT_LO12:
    case K_TLS_PC32: case K_TLS_PAGE21: case K_TLS_LO12:
        s = (uint64_t)(uintptr_t)slot(o, sym, s);
        break;
    default:
        break;
    }
    uint64_t target = s + (uint64_t)a;
    switch (k) {
    case K_ABS64: {
        memcpy(p, &target, 8);
        return 1;
    }
    case K_ABS32: {
        uint32_t v = (uint32_t)target;
        memcpy(p, &v, 4);
        return 1;
    }
    case K_CALL32: case K_PC32: case K_GOT_PC32: case K_TLS_PC32: {
        int64_t d = (int64_t)(target - pc);
        if ((d > INT32_MAX || d < INT32_MIN) && k == K_CALL32) {
            // Far (the host's code): through a stub. The field ends the
            // instruction, so the destination is `target + 4`.
            d = stub(o, sym, target + 4) - (p + 4);
        }
        if (d > INT32_MAX || d < INT32_MIN) {
            fprintf(stderr, "error: %s: a pc-relative reference out of range\n", o->what);
            return 0;
        }
        int32_t v = (int32_t)d;
        memcpy(p, &v, 4);
        return 1;
    }
    default:
        break;
    }
    uint32_t ins;
    memcpy(&ins, p, 4);
    switch (k) {
    case K_B26: {
        int64_t d = (int64_t)(target - pc);
        if (d >= (1 << 27) || d < -(1 << 27)) d = stub(o, sym, target) - p;
        ins = (ins & 0xfc000000) | ((uint32_t)(d >> 2) & 0x03ffffff);
        break;
    }
    case K_PAGE21: case K_GOT_PAGE21: case K_TLS_PAGE21: {
        int64_t pages = (int64_t)(target >> 12) - (int64_t)(pc >> 12);
        if (pages >= (1 << 20) || pages < -(1 << 20)) {
            fprintf(stderr, "error: %s: a page reference out of range\n", o->what);
            return 0;
        }
        ins = (ins & 0x9f00001f) | (((uint32_t)pages & 3) << 29) | ((((uint32_t)pages >> 2) & 0x7ffff) << 5);
        break;
    }
    case K_LO12: case K_GOT_LO12: case K_TLS_LO12: {
        uint32_t lo = (uint32_t)(target & 0xfff);
        // A load / store scales its offset by the access size.
        if ((ins & 0x3b000000) == 0x39000000) {
            uint32_t scale = ins >> 30;
            if ((ins & 0x04800000) == 0x04800000) scale = 4; // 128-bit vector
            lo >>= scale;
        }
        ins = (ins & 0xffc003ff) | ((lo & 0xfff) << 10);
        break;
    }
    default:
        return 0;
    }
    memcpy(p, &ins, 4);
    return 1;
}

#if defined(__APPLE__)
// Mach-O (MH_OBJECT): sections of the one segment; relocations per
// section, addends in the instruction (x86_64) or an ARM64_RELOC_ADDEND
// before (arm64).
static int map_object(struct obj *o, const unsigned char *buf, size_t n, const char *what) {
    memset(o, 0, sizeof *o);
    o->buf = buf;
    o->what = what;
    const struct mach_header_64 *mh = (const void *)buf;
#if defined(__x86_64__)
    const cpu_type_t cpu = CPU_TYPE_X86_64;
#else
    const cpu_type_t cpu = CPU_TYPE_ARM64;
#endif
    if (n < sizeof *mh || mh->magic != MH_MAGIC_64 || mh->cputype != cpu) {
        fprintf(stderr, "error: %s: not a Mach-O object of this machine\n", what);
        return 0;
    }
    const struct section_64 *sects = NULL;
    const struct symtab_command *st = NULL;
    const struct load_command *lc = (const void *)(mh + 1);
    for (uint32_t i = 0; i < mh->ncmds; i++, lc = (const void *)((const char *)lc + lc->cmdsize)) {
        if (lc->cmd == LC_SEGMENT_64) {
            sects = (const void *)((const struct segment_command_64 *)lc + 1);
            o->nsects = ((const struct segment_command_64 *)lc)->nsects;
        }
        if (lc->cmd == LC_SYMTAB) st = (const void *)lc;
    }
    // What runs is mapped: not debug info, unwind tables or the like.
    struct place *p = calloc(o->nsects + 1, sizeof *p);
    o->at = calloc(o->nsects + 1, sizeof *o->at);
    size_t nrel = 0;
    for (uint32_t k = 0; k < o->nsects; k++) {
        const struct section_64 *s = &sects[k];
        o->at[k] = s->addr;
        if ((s->flags & S_ATTR_DEBUG) || !strcmp(s->segname, "__LD") || !strcmp(s->sectname, "__eh_frame"))
            continue;
        p[k].size = s->size;
        p[k].align = (uint64_t)1 << s->align;
        p[k].code = (s->flags & (S_ATTR_PURE_INSTRUCTIONS | S_ATTR_SOME_INSTRUCTIONS)) != 0;
        p[k].src = (s->flags & SECTION_TYPE) == S_ZEROFILL ? NULL : buf + s->offset;
        nrel += s->nreloc;
    }
    int ok = map_sections(o, p, nrel);
    free(p);
    if (!ok) return 0;
    const struct nlist_64 *nl = st ? (const void *)(buf + st->symoff) : NULL;
    const char *strs = st ? (const char *)buf + st->stroff : "";
    alloc_syms(o, st ? st->nsyms : 0);
    for (uint32_t i = 0; i < o->nsyms; i++) {
        const struct nlist_64 *s = &nl[i];
        if ((s->n_type & N_STAB) || (s->n_type & N_TYPE) != N_SECT) continue;
        uint32_t k = s->n_sect - 1;
        if (k >= o->nsects || !o->base[k]) continue;
        def_sym(o, i, strs + s->n_un.n_strx, o->base[k] + (s->n_value - o->at[k]), s->n_type & N_EXT);
    }
    return 1;
}

static int link_object(struct obj *o) {
    const struct mach_header_64 *mh = (const void *)o->buf;
    const struct section_64 *sects = NULL;
    const struct symtab_command *st = NULL;
    const struct load_command *lc = (const void *)(mh + 1);
    for (uint32_t i = 0; i < mh->ncmds; i++, lc = (const void *)((const char *)lc + lc->cmdsize)) {
        if (lc->cmd == LC_SEGMENT_64) sects = (const void *)((const struct segment_command_64 *)lc + 1);
        if (lc->cmd == LC_SYMTAB) st = (const void *)lc;
    }
    const struct nlist_64 *nl = st ? (const void *)(o->buf + st->symoff) : NULL;
    const char *strs = st ? (const char *)o->buf + st->stroff : "";
    int ok = 1;
    jit_writable(1);
    for (uint32_t k = 0; k < o->nsects && ok; k++) {
        if (!o->base[k]) continue;
        const struct relocation_info *rel = (const void *)(o->buf + sects[k].reloff);
        for (uint32_t r = 0; r < sects[k].nreloc && ok; r++) {
            struct relocation_info ri = rel[r];
            int64_t a = 0;
#if defined(__aarch64__)
            if (ri.r_type == ARM64_RELOC_ADDEND) {
                a = ((int64_t)ri.r_symbolnum << 40) >> 40;
                ri = rel[++r];
            }
#endif
            char *p = o->base[k] + ri.r_address;
            enum kind kind;
            int tls = 0;
#if defined(__x86_64__)
            int32_t field = 0;
            if (ri.r_length == 2) memcpy(&field, p, 4);
            int extra = 0; // SIGNED_<n>: n bytes of immediate after the field
            switch (ri.r_type) {
            case X86_64_RELOC_UNSIGNED: kind = ri.r_length == 3 ? K_ABS64 : K_ABS32; break;
            case X86_64_RELOC_SIGNED: kind = K_PC32; break;
            case X86_64_RELOC_SIGNED_1: kind = K_PC32; extra = 1; break;
            case X86_64_RELOC_SIGNED_2: kind = K_PC32; extra = 2; break;
            case X86_64_RELOC_SIGNED_4: kind = K_PC32; extra = 4; break;
            case X86_64_RELOC_BRANCH: kind = K_CALL32; break;
            case X86_64_RELOC_GOT_LOAD: case X86_64_RELOC_GOT: kind = K_GOT_PC32; break;
            case X86_64_RELOC_TLV: kind = K_TLS_PC32; tls = 1; break;
            default: kind = (enum kind)-1;
            }
            if (kind == K_ABS64) {
                int64_t v;
                memcpy(&v, p, 8);
                a = v;
            } else if (kind == K_ABS32) {
                a = field;
            } else {
                // From the end of the instruction, as the field counts.
                a = (int64_t)field - 4;
            }
#else
            switch (ri.r_type) {
            case ARM64_RELOC_UNSIGNED: kind = ri.r_length == 3 ? K_ABS64 : K_ABS32; break;
            case ARM64_RELOC_BRANCH26: kind = K_B26; break;
            case ARM64_RELOC_PAGE21: kind = K_PAGE21; break;
            case ARM64_RELOC_PAGEOFF12: kind = K_LO12; break;
            case ARM64_RELOC_GOT_LOAD_PAGE21: kind = K_GOT_PAGE21; break;
            case ARM64_RELOC_GOT_LOAD_PAGEOFF12: kind = K_GOT_LO12; break;
            case ARM64_RELOC_TLVP_LOAD_PAGE21: kind = K_TLS_PAGE21; tls = 1; break;
            case ARM64_RELOC_TLVP_LOAD_PAGEOFF12: kind = K_TLS_LO12; tls = 1; break;
            default: kind = (enum kind)-1;
            }
            if (kind == K_ABS64 || kind == K_ABS32) {
                // The bytes hold the addend (section-relative: the
                // object address).
                int64_t v = 0;
                memcpy(&v, p, kind == K_ABS64 ? 8 : 4);
                if (kind == K_ABS32) v = (int32_t)v;
                a += v;
            }
#endif
            if (kind == (enum kind)-1) {
                fprintf(stderr, "error: %s: relocation type %u is not supported\n", o->what, ri.r_type);
                ok = 0;
                break;
            }
            uint64_t s;
            int64_t sym = -1;
            if (ri.r_extern) {
                sym = ri.r_symbolnum;
                s = sym_value(o, (uint32_t)sym, strs + nl[sym].n_un.n_strx, tls);
                if (!s) {
                    ok = 0;
                    break;
                }
            } else {
                uint32_t i = ri.r_symbolnum - 1;
                if (i >= o->nsects || !o->base[i]) continue;
                // Section-relative: the target's object address moved by
                // its section's.
                s = (uint64_t)(uintptr_t)o->base[i] - o->at[i];
#if defined(__x86_64__)
                if (ri.r_pcrel) {
                    // The field held target - (place + 4 + extra), both
                    // object addresses.
                    uint64_t place = o->at[k] + ri.r_address;
                    s += place + 4 + (uint64_t)extra + (uint64_t)(int64_t)field;
                    a = -4 - extra;
                }
#endif
            }
            ok = fix(o, p, kind, sym, s, a);
        }
    }
    jit_writable(0);
    flush_code(o->code, o->code_cap);
    return ok;
}
#else
// ELF (ET_REL, 64-bit little-endian): allocated sections; RELA sections
// name the section they apply to.
#if defined(__x86_64__)
#define ELF_MACHINE EM_X86_64
#else
#define ELF_MACHINE EM_AARCH64
#endif

static const Elf64_Shdr *elf_sections(const unsigned char *buf) {
    return (const void *)(buf + ((const Elf64_Ehdr *)buf)->e_shoff);
}

static int map_object(struct obj *o, const unsigned char *buf, size_t n, const char *what) {
    memset(o, 0, sizeof *o);
    o->buf = buf;
    o->what = what;
    const Elf64_Ehdr *eh = (const void *)buf;
    if (n < sizeof *eh || memcmp(eh->e_ident, ELFMAG, SELFMAG) || eh->e_ident[EI_CLASS] != ELFCLASS64 ||
        eh->e_type != ET_REL || eh->e_machine != ELF_MACHINE) {
        fprintf(stderr, "error: %s: not an ELF object of this machine\n", what);
        return 0;
    }
    const Elf64_Shdr *sh = elf_sections(buf);
    o->nsects = eh->e_shnum;
    struct place *p = calloc(o->nsects + 1, sizeof *p);
    o->at = calloc(o->nsects + 1, sizeof *o->at);
    size_t nrel = 0;
    const Elf64_Shdr *symtab = NULL;
    const char *names = (const char *)buf + sh[eh->e_shstrndx].sh_offset;
    for (uint32_t k = 0; k < o->nsects; k++) {
        const Elf64_Shdr *s = &sh[k];
        if (s->sh_type == SHT_SYMTAB) symtab = s;
        if (s->sh_type == SHT_RELA) nrel += s->sh_size / sizeof(Elf64_Rela);
        // What runs is mapped: not unwind tables, nor thread-locals (a
        // cell uses the host's).
        if (!(s->sh_flags & SHF_ALLOC) || (s->sh_flags & SHF_TLS) || !strcmp(names + s->sh_name, ".eh_frame"))
            continue;
        p[k].size = s->sh_size;
        p[k].align = s->sh_addralign ? s->sh_addralign : 1;
        p[k].code = (s->sh_flags & SHF_EXECINSTR) != 0;
        p[k].src = s->sh_type == SHT_NOBITS ? NULL : buf + s->sh_offset;
    }
    int ok = map_sections(o, p, nrel);
    free(p);
    if (!ok) return 0;
    if (!symtab) return 1;
    const Elf64_Sym *sy = (const void *)(buf + symtab->sh_offset);
    const char *strs = (const char *)buf + sh[symtab->sh_link].sh_offset;
    alloc_syms(o, (uint32_t)(symtab->sh_size / sizeof *sy));
    for (uint32_t i = 1; i < o->nsyms; i++) {
        const Elf64_Sym *s = &sy[i];
        if (s->st_shndx == SHN_UNDEF || s->st_shndx >= SHN_LORESERVE || !o->base[s->st_shndx]) continue;
        if (ELF64_ST_TYPE(s->st_info) == STT_TLS) continue;
        int global = ELF64_ST_BIND(s->st_info) != STB_LOCAL && s->st_name;
        def_sym(o, i, strs + s->st_name, o->base[s->st_shndx] + s->st_value, global);
    }
    return 1;
}

static int link_object(struct obj *o) {
    const Elf64_Ehdr *eh = (const void *)o->buf;
    const Elf64_Shdr *sh = elf_sections(o->buf);
    int ok = 1;
    jit_writable(1);
    for (uint32_t k = 0; k < o->nsects && ok; k++) {
        const Elf64_Shdr *rs = &sh[k];
        if (rs->sh_type != SHT_RELA || rs->sh_info >= eh->e_shnum || !o->base[rs->sh_info]) continue;
        const Elf64_Shdr *symtab = &sh[rs->sh_link];
        const Elf64_Sym *sy = (const void *)(o->buf + symtab->sh_offset);
        const char *strs = (const char *)o->buf + sh[symtab->sh_link].sh_offset;
        const Elf64_Rela *rel = (const void *)(o->buf + rs->sh_offset);
        for (size_t r = 0; r < rs->sh_size / sizeof *rel && ok; r++) {
            uint32_t type = ELF64_R_TYPE(rel[r].r_info), i = ELF64_R_SYM(rel[r].r_info);
            char *p = o->base[rs->sh_info] + rel[r].r_offset;
            enum kind kind;
            int tls = 0;
            switch (type) {
#if defined(__x86_64__)
            case R_X86_64_NONE: continue;
            case R_X86_64_64: kind = K_ABS64; break;
            case R_X86_64_32: case R_X86_64_32S: kind = K_ABS32; break;
            case R_X86_64_PC32: kind = K_PC32; break;
            case R_X86_64_PLT32: kind = K_CALL32; break;
            case R_X86_64_GOTPCREL: case R_X86_64_GOTPCRELX: case R_X86_64_REX_GOTPCRELX: kind = K_GOT_PC32; break;
            case R_X86_64_GOTTPOFF: kind = K_TLS_PC32; tls = 1; break;
#else
            case R_AARCH64_NONE: continue;
            case R_AARCH64_ABS64: kind = K_ABS64; break;
            case R_AARCH64_ABS32: kind = K_ABS32; break;
            case R_AARCH64_PREL32: kind = K_PC32; break;
            case R_AARCH64_CALL26: case R_AARCH64_JUMP26: kind = K_B26; break;
            case R_AARCH64_ADR_PREL_PG_HI21: kind = K_PAGE21; break;
            case R_AARCH64_ADD_ABS_LO12_NC: case R_AARCH64_LDST8_ABS_LO12_NC: case R_AARCH64_LDST16_ABS_LO12_NC:
            case R_AARCH64_LDST32_ABS_LO12_NC: case R_AARCH64_LDST64_ABS_LO12_NC: case R_AARCH64_LDST128_ABS_LO12_NC:
                kind = K_LO12; break;
            case R_AARCH64_ADR_GOT_PAGE: kind = K_GOT_PAGE21; break;
            case R_AARCH64_LD64_GOT_LO12_NC: kind = K_GOT_LO12; break;
            case R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21: kind = K_TLS_PAGE21; tls = 1; break;
            case R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC: kind = K_TLS_LO12; tls = 1; break;
#endif
            default:
                fprintf(stderr, "error: %s: relocation type %u is not supported\n", o->what, type);
                ok = 0;
                continue;
            }
            const Elf64_Sym *s = &sy[i];
            uint64_t v;
            int64_t sym = -1;
            if (ELF64_ST_BIND(s->st_info) == STB_LOCAL && ELF64_ST_TYPE(s->st_info) != STT_TLS) {
                // A section or local symbol of this object.
                if (s->st_shndx >= o->nsects || !o->base[s->st_shndx]) continue;
                v = (uint64_t)(uintptr_t)o->base[s->st_shndx] + s->st_value;
            } else {
                sym = i;
                v = sym_value(o, i, strs + s->st_name, tls);
                if (!v) {
                    ok = 0;
                    break;
                }
            }
            ok = fix(o, p, kind, sym, v, rel[r].r_addend);
        }
    }
    jit_writable(0);
    flush_code(o->code, o->code_cap);
    return ok;
}
#endif

static void free_obj(struct obj *o) {
    free(o->base);
    free(o->at);
    free(o->addr);
    free(o->got);
    free(o->stub);
}

// Map and link the cell; its entry point (NULL: failed, reported).
static void (*jit_cell(const char *obj, size_t n))(void) {
    cells++;
    struct obj o;
    int ok = map_object(&o, (const unsigned char *)obj, n, "cell") && link_object(&o) && o.entry;
    void *entry = o.entry;
    free_obj(&o);
    return ok ? (void (*)(void))entry : NULL;
}

// A prebuilt dependency's archive (BSD or GNU `ar`): every member, now
// (mapped first, so they refer to each other).
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
        // Not the symbol table (BSD `__.SYMDEF`, GNU `/` and `/SYM64/`) nor
        // GNU's long-name table `//`.
        int index = !strncmp(name, "__.SYMDEF", 9) || (name[0] == '/' && (name[1] == ' ' || name[1] == '/')) ||
                    !strncmp(name, "/SYM64/", 7);
        if (!index && len > skip) {
            if (!map_object(&objs[n], body, len - skip, path)) return 1;
            n++;
        }
        off += 60 + len;
        off += off & 1;
    }
    int bad = 0;
    for (int i = 0; i < n; i++) {
        if (!bad && !link_object(&objs[i])) bad = 1;
        free_obj(&objs[i]);
    }
    return bad;
}

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
    (void)argc;
    (void)argv;
    int ctl = dup(0);
    int nul = open("/dev/null", O_RDONLY);
    dup2(nul, 0);  // the cells' stdin
    close(nul);
    rok_runtime_init();
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
