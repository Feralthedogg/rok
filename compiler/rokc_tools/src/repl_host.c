// The `rokc repl` session host (repl.rs). One process, runtime up
// once: each cell is loaded here and run once, so earlier cells never
// run again. Commands come on the socket rokc passes as stdin: a path
// per line, a relocatable object (`.o`, loaded by `load_object` below)
// or a shared library (anything else, `dlopen`). The reply is
// `pid <p>\n` (the process running the cell) and then
// `ok <n>\n<n bytes of the shown value>`, `err\n`, or
// `unsupported <why>\n` when the object loader cannot take that object
// (nothing ran; rokc sends the cell again as a shared library).
// `SIGINT` ends a running cell (the session goes on as before it) and
// is ignored between cells.
#include <dlfcn.h>
#include <fcntl.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

void rok_runtime_init(void);

// The cell's shown value (a rok `str`), which the cell sets.
struct {
    const char *ptr;
    size_t len;
} __rok_repl_out;

// Exported symbols of the loaded objects, newest first: a later cell
// links against them (binding slots, statics), then against the host.
struct sym {
    char *name;
    void *addr;
    struct sym *next;
};
static struct sym *syms[4096];

static unsigned sym_hash(const char *s) {
    unsigned h = 2166136261u;
    while (*s) h = (h ^ (unsigned char)*s++) * 16777619u;
    return h % (sizeof syms / sizeof *syms);
}

static void sym_define(const char *name, void *addr) {
    struct sym *s = malloc(sizeof *s);
    unsigned h = sym_hash(name);
    s->name = strdup(name);
    s->addr = addr;
    s->next = syms[h];
    syms[h] = s;
}

// `name` as the linker spells it (leading `_`).
static void *sym_lookup(const char *name) {
    for (struct sym *s = syms[sym_hash(name)]; s; s = s->next)
        if (strcmp(s->name, name) == 0) return s->addr;
    return name[0] == '_' ? dlsym(RTLD_DEFAULT, name + 1) : NULL;
}

enum { LOAD_OK, LOAD_UNSUPPORTED, LOAD_ERROR };
static char why[512];

#if defined(__APPLE__) && defined(__aarch64__)
#include <libkern/OSCacheControl.h>
#include <mach-o/arm64/reloc.h>
#include <mach-o/dyld.h>
#include <mach-o/loader.h>
#include <mach-o/nlist.h>
#include <mach-o/reloc.h>

// A symbol of the host executable by its symbol table, not `dlsym`: a
// thread-local's TLVP relocation wants its descriptor, which `dlsym`
// does not give (it returns this thread's instance).
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
    // ponytail: a linear scan, for the few thread-locals a cell uses.
    for (uint32_t i = 0; i < st->nsyms; i++)
        if (!(nl[i].n_type & N_STAB) && (nl[i].n_type & N_TYPE) == N_SECT &&
            !strcmp(strs + nl[i].n_un.n_strx, name))
            return (void *)(nl[i].n_value + slide);
    return NULL;
}

#define FAIL(code, ...)                               \
    do {                                              \
        snprintf(why, sizeof why, __VA_ARGS__);       \
        status = code;                                \
        goto out;                                     \
    } while (0)

static uint64_t align_up(uint64_t x, uint64_t a) { return (x + a - 1) & ~(a - 1); }

// Load a Mach-O arm64 object (clang -c): copy its sections into fresh
// memory (code, then call stubs, then data and GOT slots), apply its
// relocations against itself, earlier cells and the host, make the code
// executable, export its external symbols, run its initializers. New
// memory, not a new file: macOS does not verify it the way it verifies
// each newly written library on first map.
static int load_object(const char *path, void (**entry)(void)) {
    int status = LOAD_OK;
    char *buf = NULL, *mem = MAP_FAILED;
    uint64_t total = 0;
    uint64_t *addr = NULL, *got = NULL, *at = NULL;
    int fd = open(path, O_RDONLY);
    struct stat sb;
    if (fd < 0 || fstat(fd, &sb) != 0) FAIL(LOAD_ERROR, "cannot open %s", path);
    buf = malloc(sb.st_size);
    if (!buf || read(fd, buf, sb.st_size) != sb.st_size) FAIL(LOAD_ERROR, "cannot read %s", path);
    const struct mach_header_64 *mh = (const void *)buf;
    if (mh->magic != MH_MAGIC_64 || mh->cputype != CPU_TYPE_ARM64 || mh->filetype != MH_OBJECT)
        FAIL(LOAD_UNSUPPORTED, "not an arm64 Mach-O object");
    const struct load_command *lc = (const void *)(mh + 1);
    const struct segment_command_64 *seg = NULL;
    const struct symtab_command *st = NULL;
    for (uint32_t i = 0; i < mh->ncmds; i++, lc = (const void *)((const char *)lc + lc->cmdsize)) {
        if (lc->cmd == LC_SEGMENT_64) seg = (const void *)lc;
        if (lc->cmd == LC_SYMTAB) st = (const void *)lc;
    }
    if (!seg || !st) FAIL(LOAD_UNSUPPORTED, "no segment or symbol table");
    const struct section_64 *sec = (const void *)(seg + 1);
    uint32_t ns = seg->nsects, nsyms = st->nsyms;
    const struct nlist_64 *nl = (const void *)(buf + st->symoff);
    const char *strs = buf + st->stroff;
    // Section offsets in the new memory (`UINT64_MAX`: not loaded).
    at = calloc(ns + 1, sizeof *at);
    addr = calloc(nsyms + 1, sizeof *addr);
    if (!at || !addr) FAIL(LOAD_ERROR, "out of memory");
    uint64_t page = (uint64_t)getpagesize(), off = 0;
    for (int code = 1; code >= 0; code--) {
        for (uint32_t i = 0; i < ns; i++) {
            uint32_t type = sec[i].flags & SECTION_TYPE;
            int is_code = (sec[i].flags & (S_ATTR_PURE_INSTRUCTIONS | S_ATTR_SOME_INSTRUCTIONS)) != 0;
            // Unwind tables are for the linker; rok does not unwind.
            if (!strcmp(sec[i].segname, "__LD") || !strcmp(sec[i].segname, "__DWARF") ||
                !strcmp(sec[i].sectname, "__eh_frame") || (sec[i].flags & S_ATTR_DEBUG)) {
                at[i] = UINT64_MAX;
                continue;
            }
            if (type >= S_THREAD_LOCAL_REGULAR && type <= S_THREAD_LOCAL_INIT_FUNCTION_POINTERS)
                FAIL(LOAD_UNSUPPORTED, "thread-local section %s", sec[i].sectname);
            if (type == S_INIT_FUNC_OFFSETS)
                FAIL(LOAD_UNSUPPORTED, "section %s", sec[i].sectname);
            if (is_code != code) continue;
            off = align_up(off, 1ull << sec[i].align);
            at[i] = off;
            off += sec[i].size;
        }
        if (code) {
            // One 16-byte call stub per symbol (`ldr x16, 8; br x16; .quad`).
            off = align_up(off, 16);
            uint64_t stubs = off;
            off = align_up(off + 16ull * nsyms, page);
            at[ns] = stubs;  // the stubs' offset
            total = off;     // the code's end
        }
    }
    off = align_up(off, 8);
    uint64_t got_off = off;
    off = align_up(off + 8ull * nsyms, page);
    uint64_t text_size = total;
    total = off;
    mem = mmap(NULL, total, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON, -1, 0);
    if (mem == MAP_FAILED) FAIL(LOAD_ERROR, "cannot map %llu bytes", (unsigned long long)total);
    got = (uint64_t *)(mem + got_off);
    uint32_t *stub = (uint32_t *)(mem + at[ns]);
    for (uint32_t i = 0; i < ns; i++) {
        uint32_t type = sec[i].flags & SECTION_TYPE;
        if (at[i] == UINT64_MAX || type == S_ZEROFILL || type == S_GB_ZEROFILL) continue;
        memcpy(mem + at[i], buf + sec[i].offset, sec[i].size);
    }
    // Symbol addresses: defined here, or found when first used.
    for (uint32_t i = 0; i < nsyms; i++) {
        uint8_t t = nl[i].n_type;
        if (t & N_STAB) continue;
        if ((t & N_TYPE) == N_SECT && nl[i].n_sect && at[nl[i].n_sect - 1] != UINT64_MAX)
            addr[i] = (uint64_t)mem + at[nl[i].n_sect - 1] + nl[i].n_value - sec[nl[i].n_sect - 1].addr;
        else if ((t & N_TYPE) == N_ABS)
            addr[i] = nl[i].n_value;
        else if ((t & N_TYPE) == N_UNDF && nl[i].n_value)
            FAIL(LOAD_UNSUPPORTED, "common symbol %s", strs + nl[i].n_un.n_strx);
    }
#define SYM(i)                                                                        \
    (addr[i] ? addr[i]                                                               \
             : (addr[i] = (uint64_t)sym_lookup(strs + nl[i].n_un.n_strx))             \
                   ? addr[i]                                                         \
                   : (status = LOAD_ERROR,                                           \
                      snprintf(why, sizeof why, "undefined symbol %s", strs + nl[i].n_un.n_strx), 0))
    for (uint32_t s = 0; s < ns; s++) {
        if (at[s] == UINT64_MAX) continue;
        const struct relocation_info *rel = (const void *)(buf + sec[s].reloff);
        int64_t addend = 0;
        for (uint32_t k = 0; k < sec[s].nreloc; k++) {
            struct relocation_info r = rel[k];
            if (r.r_address & R_SCATTERED) FAIL(LOAD_UNSUPPORTED, "scattered relocation");
            char *loc = mem + at[s] + r.r_address;
            uint32_t *insn = (uint32_t *)loc;
            uint64_t target = 0;
            if (r.r_type == ARM64_RELOC_ADDEND) {
                addend = ((int64_t)r.r_symbolnum << 40) >> 40;  // 24-bit signed
                continue;
            }
            if (r.r_extern) {
                if (!SYM(r.r_symbolnum)) goto out;
                target = addr[r.r_symbolnum] + addend;
            } else if (r.r_type != ARM64_RELOC_UNSIGNED)
                FAIL(LOAD_UNSUPPORTED, "section-relative relocation %u", r.r_type);
            switch (r.r_type) {
            case ARM64_RELOC_UNSIGNED: {
                uint64_t v = r.r_length == 3 ? *(uint64_t *)loc : *(uint32_t *)loc;
                if (r.r_extern)
                    v = target + v;
                else {
                    uint32_t k2 = r.r_symbolnum - 1;
                    if (at[k2] == UINT64_MAX) FAIL(LOAD_UNSUPPORTED, "pointer into a dropped section");
                    v = v - sec[k2].addr + (uint64_t)mem + at[k2];
                }
                if (r.r_length == 3)
                    *(uint64_t *)loc = v;
                else if (r.r_length == 2)
                    *(uint32_t *)loc = (uint32_t)v;
                else
                    FAIL(LOAD_UNSUPPORTED, "pointer of length %u", r.r_length);
                break;
            }
            case ARM64_RELOC_BRANCH26: {
                if ((nl[r.r_symbolnum].n_type & N_TYPE) == N_UNDF) {
                    // Out of range (the host, earlier cells): via a stub.
                    uint32_t *st16 = stub + 4 * r.r_symbolnum;
                    st16[0] = 0x58000050;  // ldr x16, #8
                    st16[1] = 0xd61f0200;  // br x16
                    memcpy(st16 + 2, &target, 8);
                    target = (uint64_t)st16;
                }
                int64_t d = (int64_t)(target - (uint64_t)loc);
                if (d >= (1 << 27) || d < -(1 << 27)) FAIL(LOAD_UNSUPPORTED, "branch out of range");
                *insn = (*insn & 0xfc000000) | (((uint64_t)d >> 2) & 0x03ffffff);
                break;
            }
            case ARM64_RELOC_GOT_LOAD_PAGE21:
            case ARM64_RELOC_GOT_LOAD_PAGEOFF12:
            case ARM64_RELOC_TLVP_LOAD_PAGE21:
            case ARM64_RELOC_TLVP_LOAD_PAGEOFF12:
            case ARM64_RELOC_PAGE21:
            case ARM64_RELOC_PAGEOFF12: {
                int tlv = r.r_type == ARM64_RELOC_TLVP_LOAD_PAGE21 || r.r_type == ARM64_RELOC_TLVP_LOAD_PAGEOFF12;
                if (tlv || r.r_type == ARM64_RELOC_GOT_LOAD_PAGE21 || r.r_type == ARM64_RELOC_GOT_LOAD_PAGEOFF12) {
                    // A slot holding the address (a thread-local's: its
                    // descriptor in the host).
                    if (!got[r.r_symbolnum]) {
                        if (tlv) {
                            const char *n = strs + nl[r.r_symbolnum].n_un.n_strx;
                            got[r.r_symbolnum] = (uint64_t)host_symbol(n);
                            if (!got[r.r_symbolnum]) FAIL(LOAD_UNSUPPORTED, "thread-local %s", n);
                        } else
                            got[r.r_symbolnum] = target;
                    }
                    target = (uint64_t)&got[r.r_symbolnum];
                }
                if (r.r_type == ARM64_RELOC_PAGE21 || r.r_type == ARM64_RELOC_GOT_LOAD_PAGE21 ||
                    r.r_type == ARM64_RELOC_TLVP_LOAD_PAGE21) {
                    int64_t pages = (int64_t)((target >> 12) - ((uint64_t)loc >> 12));
                    if (pages >= (1 << 20) || pages < -(1 << 20)) FAIL(LOAD_UNSUPPORTED, "page out of range");
                    *insn = (*insn & 0x9f00001f) | (((uint32_t)pages & 3) << 29) |
                            ((((uint32_t)pages >> 2) & 0x7ffff) << 5);
                } else {
                    uint32_t lo = target & 0xfff, scale = 0;
                    if ((*insn & 0x3b000000) == 0x39000000) {  // load / store
                        scale = *insn >> 30;
                        if ((*insn & 0x04800000) == 0x04800000) scale = 4;  // 128-bit
                    } else if ((*insn & 0x1f000000) != 0x11000000)  // not add
                        FAIL(LOAD_UNSUPPORTED, "page offset on instruction %08x", *insn);
                    if (lo & ((1u << scale) - 1)) FAIL(LOAD_UNSUPPORTED, "misaligned page offset");
                    *insn = (*insn & ~(0xfffu << 10)) | ((lo >> scale) << 10);
                }
                break;
            }
            default:
                FAIL(LOAD_UNSUPPORTED, "relocation type %u", r.r_type);
            }
            addend = 0;
        }
    }
    if (mprotect(mem, text_size, PROT_READ | PROT_EXEC) != 0) FAIL(LOAD_ERROR, "cannot make code executable");
    sys_icache_invalidate(mem, text_size);
    *entry = NULL;
    for (uint32_t i = 0; i < nsyms; i++) {
        const char *n = strs + nl[i].n_un.n_strx;
        if ((nl[i].n_type & (N_STAB | N_TYPE | N_EXT)) != (N_SECT | N_EXT) || !addr[i]) continue;
        sym_define(n, (void *)addr[i]);
        if (!strcmp(n, "_rok_repl_cell")) *entry = (void (*)(void))addr[i];
    }
    for (uint32_t i = 0; i < ns; i++)
        if (at[i] != UINT64_MAX && (sec[i].flags & SECTION_TYPE) == S_MOD_INIT_FUNC_POINTERS)
            for (uint64_t k = 0; k < sec[i].size / 8; k++) ((void (**)(void))(mem + at[i]))[k]();
    if (!*entry) FAIL(LOAD_ERROR, "no rok_repl_cell in %s", path);
    mem = MAP_FAILED;  // kept: the cell's code and data live on
out:
    if (mem != MAP_FAILED) munmap(mem, total);
    if (fd >= 0) close(fd);
    free(buf);
    free(addr);
    free(at);
    return status;
}
#else
// ponytail: ELF (and x86_64 Mach-O) objects are left to `dlopen`.
static int load_object(const char *path, void (**entry)(void)) {
    (void)path;
    (void)entry;
    snprintf(why, sizeof why, "no object loader for this platform");
    return LOAD_UNSUPPORTED;
}
#endif

int main(void) {
    int ctl = dup(0);
    int nul = open("/dev/null", O_RDONLY);
    dup2(nul, 0);  // the cells' stdin
    close(nul);
    rok_runtime_init();
    signal(SIGINT, SIG_IGN);
    for (;;) {
        char path[4096], c;
        size_t n = 0;
        while (read(ctl, &c, 1) == 1 && c != '\n')
            if (n < sizeof path - 1) path[n++] = c;
        if (n == 0) return 0;
        path[n] = 0;
        fflush(stdout);
        // A copy of the session from before the cell. When the cell's
        // process dies (panic, signal, exit) the copy carries on as the
        // session; otherwise it is told to go.
        // ponytail: threads other than this one are not in the copy.
        int verdict[2];
        if (pipe(verdict) != 0) return 1;
        pid_t snap = fork();
        if (snap == 0) {
            close(verdict[1]);
            ssize_t r;
            while ((r = read(verdict[0], &c, 1)) < 0) {}
            if (r == 1) _exit(0);
            close(verdict[0]);
            dprintf(ctl, "err\n");
            continue;
        }
        close(verdict[0]);
        dprintf(ctl, "pid %d\n", (int)getpid());
        signal(SIGINT, SIG_DFL);
        void (*cell)(void) = NULL;
        int obj = n > 2 && !strcmp(path + n - 2, ".o");
        int st = LOAD_OK;
        if (obj) {
            st = load_object(path, &cell);
            if (st == LOAD_ERROR) fprintf(stderr, "error: %s\n", why);
        } else {
            void *lib = dlopen(path, RTLD_NOW | RTLD_GLOBAL);
            cell = lib ? (void (*)(void))dlsym(lib, "rok_repl_cell") : NULL;
            if (!cell) fprintf(stderr, "error: %s\n", dlerror());
        }
        __rok_repl_out.len = 0;
        if (cell) cell();
        signal(SIGINT, SIG_IGN);
        fflush(stdout);
        if (write(verdict[1], "", 1) != 1) {}
        close(verdict[1]);
        if (snap > 0) waitpid(snap, NULL, 0);
        if (st == LOAD_UNSUPPORTED) {
            dprintf(ctl, "unsupported %s\n", why);
            continue;
        }
        if (!cell) {
            dprintf(ctl, "err\n");
            continue;
        }
        dprintf(ctl, "ok %zu\n", __rok_repl_out.len);
        if (write(ctl, __rok_repl_out.ptr, __rok_repl_out.len) < 0) return 1;
    }
}
