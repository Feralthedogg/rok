// The `rokc repl` session host (repl.rs). One process, runtime up
// once: each cell is a shared library loaded here and run once, so
// earlier cells never run again. Commands come on the socket rokc
// passes as stdin: a library path per line; the reply is
// `ok <n>\n<n bytes of the shown value>` or `err\n`.
#include <dlfcn.h>
#include <fcntl.h>
#include <stdio.h>
#include <sys/wait.h>
#include <unistd.h>

void rok_runtime_init(void);

// The cell's shown value (a rok `str`), which the cell sets.
struct {
    const char *ptr;
    size_t len;
} __rok_repl_out;

int main(void) {
    int ctl = dup(0);
    int nul = open("/dev/null", O_RDONLY);
    dup2(nul, 0);  // the cells' stdin
    close(nul);
    rok_runtime_init();
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
        void *lib = dlopen(path, RTLD_NOW | RTLD_GLOBAL);
        void (*cell)(void) = lib ? (void (*)(void))dlsym(lib, "rok_repl_cell") : NULL;
        __rok_repl_out.len = 0;
        if (cell)
            cell();
        else
            fprintf(stderr, "error: %s\n", dlerror());
        fflush(stdout);
        if (write(verdict[1], "", 1) != 1) {}
        close(verdict[1]);
        if (snap > 0) waitpid(snap, NULL, 0);
        if (!cell) {
            dprintf(ctl, "err\n");
            continue;
        }
        dprintf(ctl, "ok %zu\n", __rok_repl_out.len);
        if (write(ctl, __rok_repl_out.ptr, __rok_repl_out.len) < 0) return 1;
    }
}
