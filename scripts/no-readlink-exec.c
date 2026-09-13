#define _GNU_SOURCE

#include <dlfcn.h>
#include <errno.h>
#include <stdio.h>
#include <string.h>
#include <sys/types.h>
#include <unistd.h>

/*
 * Adversarial preload used only by certification. It reproduces the actual
 * locked-down-sandbox failure mode by denying readlink("/proc/<pid>/exe") for
 * the current process while delegating every other readlink unchanged.
 *
 * The portable Lean compatibility shim is loaded before this library. A direct
 * Lean invocation with this adversary must fail; the portable wrapper must pass.
 */

typedef ssize_t (*readlink_fn)(const char *, char *, size_t);

static int is_current_process_exe(const char *path) {
    char expected[64];
    int n = snprintf(expected, sizeof(expected), "/proc/%ld/exe", (long)getpid());
    return n > 0 && (size_t)n < sizeof(expected) && strcmp(path, expected) == 0;
}

static readlink_fn resolve_real_readlink(void) {
    static readlink_fn fn = NULL;
    if (fn == NULL) {
        void *symbol = dlsym(RTLD_NEXT, "readlink");
        memcpy(&fn, &symbol, sizeof(fn));
    }
    return fn;
}

ssize_t readlink(const char *restrict path, char *restrict buffer, size_t size) {
    if (is_current_process_exe(path)) {
        errno = EPERM;
        return -1;
    }

    readlink_fn real_readlink = resolve_real_readlink();
    if (real_readlink == NULL) {
        errno = ENOSYS;
        return -1;
    }
    return real_readlink(path, buffer, size);
}
