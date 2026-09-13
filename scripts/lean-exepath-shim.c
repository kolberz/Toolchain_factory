#define _GNU_SOURCE

#include <dlfcn.h>
#include <errno.h>
#include <stdio.h>
#include <string.h>
#include <sys/auxv.h>
#include <sys/types.h>
#include <unistd.h>

/*
 * Lean's Linux IO.appPath implementation resolves /proc/<pid>/exe with
 * readlink(2). Some locked-down sandboxes deny that lookup before Lean can
 * initialize its search path. This narrowly-scoped preload shim replaces only
 * the current process' /proc/<pid>/exe readlink with the executable name that
 * Linux already supplied in the ELF auxiliary vector (AT_EXECFN).
 *
 * All other readlink calls are delegated unchanged to libc. Because AT_EXECFN
 * belongs to the current process, children that inherit LD_PRELOAD still obtain
 * their own executable path rather than their parent's path.
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
    if (path != NULL && buffer != NULL && is_current_process_exe(path)) {
        const char *execfn = (const char *)getauxval(AT_EXECFN);
        if (execfn != NULL && execfn[0] != '\0') {
            size_t len = strlen(execfn);
            size_t copied = len < size ? len : size;
            memcpy(buffer, execfn, copied);
            return (ssize_t)copied;
        }
    }

    readlink_fn real_readlink = resolve_real_readlink();
    if (real_readlink == NULL) {
        errno = ENOSYS;
        return -1;
    }
    return real_readlink(path, buffer, size);
}
