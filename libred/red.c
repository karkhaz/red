/*  Copyright (C) 2012-2015 by László Nagy
    This file is part of Bear.

    Bear is a tool to generate compilation database for clang tooling.

    Bear is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Bear is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

/**
 * This file implements a shared library. This library can be pre-loaded by
 * the dynamic linker of the Operating System (OS). It implements a few function
 * related to process creation. By pre-load this library the executed process
 * uses these functions instead of those from the standard library.
 *
 * The idea here is to inject a logic before call the real methods. The logic is
 * to dump the call into a file. To call the real method this library is doing
 * the job of the dynamic linker.
 *
 * The only input for the log writing is about the destination directory.
 * This is passed as environment variable.
 */

#include "config.h"

#include <stddef.h>
#include <stdarg.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <dlfcn.h>
#include <pthread.h>
#include <linux/unistd.h>
#include <sys/time.h>

#define str(s) #s
#define xstr(s) str(s)

#define array_size(a) (sizeof(a) / sizeof(a[0]))

/* Redirection of tool invocations that match absolute prefixes */
static char const *prefixes[] = {
  "/usr/bin",
  "/bin",
  "/usr/sbin"
};

static char const *transform_invocation(char const *original);

static char const *const red_known_good_path =
#ifdef RED_ENSURE_PATH
  "PATH=" xstr(RED_ENSURE_PATH) ":/usr/local/sbin:/usr/local/bin:"
  "/usr/sbin:/usr/bin:/sbin:/bin";
#else
  "PATH=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin";
#endif

#if defined HAVE_POSIX_SPAWN || defined HAVE_POSIX_SPAWNP
#include <spawn.h>
#endif

#if defined HAVE_NSGETENVIRON
#include <crt_externs.h>
static char **environ;
#else
extern char **environ;
#endif

#define ENV_OUTPUT "RED_OUTPUT"
#ifdef APPLE
# define ENV_FLAT    "DYLD_FORCE_FLAT_NAMESPACE"
# define ENV_PRELOAD "DYLD_INSERT_LIBRARIES"
# define ENV_SIZE 3
#else
# define ENV_PRELOAD "LD_PRELOAD"
# define ENV_SIZE 2
#endif

#define DLSYM(TYPE_, VAR_, SYMBOL_)                                            \
    union {                                                                    \
        void *from;                                                            \
        TYPE_ to;                                                              \
    } cast;                                                                    \
    if (0 == (cast.from = dlsym(RTLD_NEXT, SYMBOL_))) {                        \
        perror("red: dlsym");                                                 \
        exit(EXIT_FAILURE);                                                    \
    }                                                                          \
    TYPE_ const VAR_ = cast.to;


typedef char const * red_env_t[ENV_SIZE];

static int red_capture_env_t(red_env_t *env);
static void red_release_env_t(red_env_t *env);
static char const **red_update_environment(char *const envp[], red_env_t *env);
static char const **red_update_environ(char const **in, char const *key, char const *value);
static void red_report_call(char const *fun, char const *const argv[],
    long long timestamp);
static char const **red_strings_build(char const *arg, va_list *ap);
static char const **red_strings_copy(char const **const in);
static char const **red_strings_append(char const **in, char const *e);
static size_t red_strings_length(char const *const *in);
static void red_strings_release(char const **);

static int const GS = 0x1d;
static int const RS = 0x1e;
static int const US = 0x1f;

static void log_exit(int rc);
static long long get_timestamp();

static void red_ensure_path(char const **const env);
static void red_log_error(char const *category, char const *info);


static red_env_t env_names =
    { ENV_OUTPUT
    , ENV_PRELOAD
#ifdef ENV_FLAT
    , ENV_FLAT
#endif
    };

static red_env_t initial_env =
    { 0
    , 0
#ifdef ENV_FLAT
    , 0
#endif
    };

static int initialized = 0;
static pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;

static void on_load(void) __attribute__((constructor));
static void on_unload(void) __attribute__((destructor));


#ifdef HAVE_EXECVE
static int call_execve(const char *path, char *const argv[],
                       char *const envp[]);
#endif
#ifdef HAVE_EXECVP
static int call_execvp(const char *file, char *const argv[]);
#endif
#ifdef HAVE_EXECVPE
static int call_execvpe(const char *file, char *const argv[],
                        char *const envp[]);
#endif
#ifdef HAVE_EXECVP2
static int call_execvP(const char *file, const char *search_path,
                       char *const argv[]);
#endif
#ifdef HAVE_POSIX_SPAWN
static int call_posix_spawn(pid_t *restrict pid, const char *restrict path,
                            const posix_spawn_file_actions_t *file_actions,
                            const posix_spawnattr_t *restrict attrp,
                            char *const argv[restrict],
                            char *const envp[restrict]);
#endif
#ifdef HAVE_POSIX_SPAWNP
static int call_posix_spawnp(pid_t *restrict pid, const char *restrict file,
                             const posix_spawn_file_actions_t *file_actions,
                             const posix_spawnattr_t *restrict attrp,
                             char *const argv[restrict],
                             char *const envp[restrict]);
#endif


/* Initialization method to Captures the relevant environment variables.
 */

static void on_load(void) {
    pthread_mutex_lock(&mutex);
#ifdef HAVE_NSGETENVIRON
    environ = *_NSGetEnviron();
#endif
    if (!initialized)
        initialized = red_capture_env_t(&initial_env);
    pthread_mutex_unlock(&mutex);
}

static void on_unload(void) {
    pthread_mutex_lock(&mutex);
    red_release_env_t(&initial_env);
    initialized = 0;
    pthread_mutex_unlock(&mutex);
}


/* These are the methods we are try to hijack.
 */


__THROW __attribute ((__noreturn__))
void exit(int status){
  log_exit(status);
  typedef void (*func)(int);
  DLSYM(func, fp, "exit");
  (*fp)(status);
}


__THROW __attribute ((__noreturn__))
void _exit(int status){
  log_exit(status);
  typedef void (*func)(int);
  DLSYM(func, fp, "_exit");
  (*fp)(status);
}


void log_exit(int rc){
  if (!initialized)
      return;
  pthread_mutex_lock(&mutex);
  char const * const out_dir = initial_env[0];
  size_t const path_max_length = strlen(out_dir) + 32;
  char filename[path_max_length];
  if (-1 == snprintf(filename, path_max_length, "%s/%d.cmd", out_dir, getpid())) {
      perror("red: snprintf");
      exit(EXIT_FAILURE);
  }
  FILE * fd = fopen(filename, "a+");
  if (0 == fd) {
      perror("red: fopen");
      exit(EXIT_FAILURE);
  }
  fprintf(fd, "EXIT%c", RS);
  fprintf(fd, "%d%c", getpid(), RS);
  fprintf(fd, "%d%c", getppid(), RS);
  fprintf(fd, "%d%c", rc, RS);
  fprintf(fd, "%c", GS);
  if (fclose(fd)) {
      perror("red: fclose");
      exit(EXIT_FAILURE);
  }
  pthread_mutex_unlock(&mutex);
}


static long long get_timestamp(){
    struct timeval tv;
    if (gettimeofday(&tv, NULL)){
      perror("red: gettimeofday");
      exit(EXIT_FAILURE);
    }
    long long timestamp = (tv.tv_sec) * 1000 + (tv.tv_usec) / 1000;
    return timestamp;
}


#ifdef HAVE_EXECVE
int execve(const char *path, char *const argv[], char *const envp[]) {
    red_report_call(__func__, (char const *const *)argv, get_timestamp());
    return call_execve(path, argv, envp);
}
#endif

#ifdef HAVE_EXECV
#ifndef HAVE_EXECVE
#error can not implement execv without execve
#endif
int execv(const char *path, char *const argv[]) {
    red_report_call(__func__, (char const *const *)argv, get_timestamp());
    return call_execve(path, argv, environ);
}
#endif

#ifdef HAVE_EXECVPE
int execvpe(const char *file, char *const argv[], char *const envp[]) {
    red_report_call(__func__, (char const *const *)argv, get_timestamp());
    return call_execvpe(file, argv, envp);
}
#endif

#ifdef HAVE_EXECVP
int execvp(const char *file, char *const argv[]) {
    red_report_call(__func__, (char const *const *)argv, get_timestamp());
    return call_execvp(file, argv);
}
#endif

#ifdef HAVE_EXECVP2
int execvP(const char *file, const char *search_path, char *const argv[]) {
    red_report_call(__func__, (char const *const *)argv, get_timestamp());
    return call_execvP(file, search_path, argv);
}
#endif

#ifdef HAVE_EXECL
#ifndef HAVE_EXECVE
#error can not implement execl without execve
#endif
int execl(const char *path, const char *arg, ...) {
    va_list args;
    va_start(args, arg);
    char const **argv = red_strings_build(arg, &args);
    va_end(args);

    red_report_call(__func__, (char const *const *)argv, get_timestamp());
    int const result = call_execve(path, (char *const *)argv, environ);

    red_strings_release(argv);
    return result;
}
#endif

#ifdef HAVE_EXECLP
#ifndef HAVE_EXECVP
#error can not implement execlp without execvp
#endif
int execlp(const char *file, const char *arg, ...) {
    va_list args;
    va_start(args, arg);
    char const **argv = red_strings_build(arg, &args);
    va_end(args);

    red_report_call(__func__, (char const *const *)argv, get_timestamp());
    int const result = call_execvp(file, (char *const *)argv);

    red_strings_release(argv);
    return result;
}
#endif

#ifdef HAVE_EXECLE
#ifndef HAVE_EXECVE
#error can not implement execle without execve
#endif
// int execle(const char *path, const char *arg, ..., char * const envp[]);
int execle(const char *path, const char *arg, ...) {
    va_list args;
    va_start(args, arg);
    char const **argv = red_strings_build(arg, &args);
    char const **envp = va_arg(args, char const **);
    va_end(args);

    red_report_call(__func__, (char const *const *)argv, get_timestamp());
    int const result =
        call_execve(path, (char *const *)argv, (char *const *)envp);

    red_strings_release(argv);
    return result;
}
#endif

#ifdef HAVE_POSIX_SPAWN
int posix_spawn(pid_t *restrict pid, const char *restrict path,
                const posix_spawn_file_actions_t *file_actions,
                const posix_spawnattr_t *restrict attrp,
                char *const argv[restrict], char *const envp[restrict]) {
    red_report_call(__func__, (char const *const *)argv, get_timestamp());
    return call_posix_spawn(pid, path, file_actions, attrp, argv, envp);
}
#endif

#ifdef HAVE_POSIX_SPAWNP
int posix_spawnp(pid_t *restrict pid, const char *restrict file,
                 const posix_spawn_file_actions_t *file_actions,
                 const posix_spawnattr_t *restrict attrp,
                 char *const argv[restrict], char *const envp[restrict]) {
    red_report_call(__func__, (char const *const *)argv, get_timestamp());
    return call_posix_spawnp(pid, file, file_actions, attrp, argv, envp);
}
#endif

/* These are the methods which forward the call to the standard implementation.
 */

#ifdef HAVE_EXECVE
static int call_execve(const char *path, char *const argv[],
                       char *const envp[]) {
    typedef int (*func)(const char *, char *const *, char *const *);

    DLSYM(func, fp, "execve");

    char const **const menvp = red_update_environment(envp, &initial_env);
    red_ensure_path(menvp);

    path = transform_invocation(path);
    *argv[0] = *transform_invocation(argv[0]);

    int const result = (*fp)(path, argv, (char *const *)menvp);
    red_strings_release(menvp);
    return result;
}
#endif

#ifdef HAVE_EXECVPE
static int call_execvpe(const char *file, char *const argv[],
                        char *const envp[]) {
    typedef int (*func)(const char *, char *const *, char *const *);

    DLSYM(func, fp, "execvpe");

    char const **const menvp = red_update_environment(envp, &initial_env);
    red_ensure_path(menvp);

    file = transform_invocation(file);
    *argv[0] = *transform_invocation(argv[0]);

    int const result = (*fp)(file, argv, (char *const *)menvp);
    red_strings_release(menvp);
    return result;
}
#endif

#ifdef HAVE_EXECVP
static int call_execvp(const char *file, char *const argv[]) {
    typedef int (*func)(const char *file, char *const argv[]);

    DLSYM(func, fp, "execvp");

    char **const original = environ;
    char const **const modified = red_update_environment(original, &initial_env);
    red_ensure_path(modified);
    environ = (char **)modified;

    file = transform_invocation(file);
    *argv[0] = *transform_invocation(argv[0]);

    int const result = (*fp)(file, argv);
    environ = original;
    red_strings_release(modified);

    return result;
}
#endif

#ifdef HAVE_EXECVP2
static int call_execvP(const char *file, const char *search_path,
                       char *const argv[]) {
    typedef int (*func)(const char *, const char *, char *const *);

    DLSYM(func, fp, "execvP");

    char **const original = environ;
    char const **const modified = red_update_environment(original, &initial_env);

    red_ensure_path(modified);

    file = transform_invocation(file);
    *argv[0] = *transform_invocation(argv[0]);

    environ = (char **)modified;
    int const result = (*fp)(file, search_path, argv);
    environ = original;
    red_strings_release(modified);

    return result;
}
#endif

#ifdef HAVE_POSIX_SPAWN
static int call_posix_spawn(pid_t *restrict pid, const char *restrict path,
                            const posix_spawn_file_actions_t *file_actions,
                            const posix_spawnattr_t *restrict attrp,
                            char *const argv[restrict],
                            char *const envp[restrict]) {
    typedef int (*func)(pid_t *restrict, const char *restrict,
                        const posix_spawn_file_actions_t *,
                        const posix_spawnattr_t *restrict,
                        char *const *restrict, char *const *restrict);

    DLSYM(func, fp, "posix_spawn");

    char const **const menvp = red_update_environment(envp, &initial_env);
    red_ensure_path(menvp);

    path = transform_invocation(path);
    *argv[0] = *transform_invocation(argv[0]);

    int const result =
        (*fp)(pid, path, file_actions, attrp, argv, (char *const *restrict)menvp);
    red_strings_release(menvp);
    return result;
}
#endif

#ifdef HAVE_POSIX_SPAWNP
static int call_posix_spawnp(pid_t *restrict pid, const char *restrict file,
                             const posix_spawn_file_actions_t *file_actions,
                             const posix_spawnattr_t *restrict attrp,
                             char *const argv[restrict],
                             char *const envp[restrict]) {
    typedef int (*func)(pid_t *restrict, const char *restrict,
                        const posix_spawn_file_actions_t *,
                        const posix_spawnattr_t *restrict,
                        char *const *restrict, char *const *restrict);

    DLSYM(func, fp, "posix_spawnp");

    char const **const menvp = red_update_environment(envp, &initial_env);
    red_ensure_path(menvp);

    file = transform_invocation(file);
    *argv[0] = *transform_invocation(argv[0]);

    int const result =
        (*fp)(pid, file, file_actions, attrp, argv, (char *const *restrict)menvp);
    red_strings_release(menvp);
    return result;
}
#endif

#define redirect_tool(tool, replacement)                                \
  do {                                                                  \
    for (int i = 0; i < array_size(prefixes); ++i) {                    \
      /* First, check if the first chars of the invoked tool matches    \
       * an absolute path prefix. */                                    \
      if (strncmp(original, prefixes[i], strlen(prefixes[i]))) {        \
        continue;                                                       \
      }                                                                 \
                                                                        \
      /* Now check if the _next_ chars of the invoked tool match the    \
       * tool that we're looking for. Use strcmp rather than strncmp    \
       * since this should also take us to the end of the string. The   \
       * '+ 1' is so that we skip the slash between the prefix and the  \
       * binary name. */                                                \
      if (strcmp(original + strlen(prefixes[i]) + 1, tool)) {           \
        continue;                                                       \
      }                                                                 \
                                                                        \
      /* `original` is equal to `prefixes[i] + / + tool`. Write a       \
       * warning and redirect the invocation.                           \
       */                                                               \
      char buf[128];                                                    \
      snprintf(buf, 128, "%s\n%s", original, xstr(replacement));        \
      red_log_error("hardcoded invocation", buf);                       \
      return xstr(replacement);                                         \
    }                                                                   \
  } while (0);


static char const *transform_invocation(char const *original) {
#ifdef RED_AR
  redirect_tool("ar", RED_AR)
#endif
#ifdef RED_AS
  redirect_tool("as", RED_AS)
#endif
#ifdef RED_ADDR2LINE
  redirect_tool("addr2line", RED_ADDR2LINE)
#endif
#ifdef RED_CATCHSEGV
  redirect_tool("catchsegv", RED_CATCHSEGV)
#endif
#ifdef RED_CPPFILT
  redirect_tool("c++filt", RED_CPPFILT)
#endif
#ifdef RED_CC
  redirect_tool("cc", RED_CC)
#endif
#ifdef RED_CLANG
  redirect_tool("clang", RED_CLANG)
#endif
#ifdef RED_CLANGPP
  redirect_tool("clang++", RED_CLANGPP)
#endif
#ifdef RED_CPP
  redirect_tool("cpp", RED_CPP)
#endif
#ifdef RED_DWP
  redirect_tool("dwp", RED_DWP)
#endif
#ifdef RED_ELFEDIT
  redirect_tool("elfedit", RED_ELFEDIT)
#endif
#ifdef RED_GENCAT
  redirect_tool("gencat", RED_GENCAT)
#endif
#ifdef RED_GETCONF
  redirect_tool("getconf", RED_GETCONF)
#endif
#ifdef RED_GETENT
  redirect_tool("getent", RED_GETENT)
#endif
#ifdef RED_GCOV
  redirect_tool("gcov", RED_GCOV)
#endif
#ifdef RED_GPP
  redirect_tool("g++", RED_GPP)
#endif
#ifdef RED_GCC
  redirect_tool("gcc", RED_GCC)
#endif
#ifdef RED_GDB
  redirect_tool("gdb", RED_GDB)
#endif
#ifdef RED_GPROF
  redirect_tool("gprof", RED_GPROF)
#endif
#ifdef RED_ICONV
  redirect_tool("iconv", RED_ICONV)
#endif
#ifdef RED_LD
  redirect_tool("ld", RED_LD)
#endif
#ifdef RED_NM
  redirect_tool("nm", RED_NM)
#endif
#ifdef RED_OBJCOPY
  redirect_tool("objcopy", RED_OBJCOPY)
#endif
#ifdef RED_OBJDUMP
  redirect_tool("objdump", RED_OBJDUMP)
#endif
#ifdef RED_RANLIB
  redirect_tool("ranlib", RED_RANLIB)
#endif
#ifdef RED_READELF
  redirect_tool("readelf", RED_READELF)
#endif
#ifdef RED_SCAN_BUILD
  redirect_tool("scan-build", RED_SCAN_BUILD)
#endif
#ifdef RED_SCAN_VIEW
  redirect_tool("scan-view", RED_SCAN_VIEW)
#endif
#ifdef RED_SIZE
  redirect_tool("size", RED_SIZE)
#endif
#ifdef RED_STRINGS
  redirect_tool("strings", RED_STRINGS)
#endif
#ifdef RED_STRIP
  redirect_tool("strip", RED_STRIP)
#endif

  return original;
}


static void red_log_error(char const *category, char const *info) {
    char error_template[] = "/tmp/red-error-XXXXXX";
    int fd = mkstemp(error_template);
    if (fd == -1) {
      perror("red: mkstemp");
      exit(1);
    }
    dprintf(fd, "%s\n%ld\n%s\n", category, (long)getpid(), info);
    if (close(fd) == -1) {
      perror("red: close");
      exit(1);
    }
}


/* If ENSURE_PATH is defined, this function checks to see if the first
 * directory in $PATH is equal to ENSURE_PATH.  If it is, this function
 * does not change envp. Otherwise, a warning is logged to a file.
 * Additionally,
 * - If ENSURE_PATH is not the first path in $PATH, this function adds it.
 * - If $PATH is empty, this function fills out $PATH with a known-good
 *   value.
 * - If $PATH is not in envp, this function can do nothing more than log
 *   a warning, as envp is a const *.
 */
static void red_ensure_path(char const **const envp) {
#ifdef RED_ENSURE_PATH
  for (char const **ptr = envp; ptr != NULL; ++ptr) {
    if (strncmp(*ptr, "PATH", 4)) {
      continue;
    }
    char *colon = strchr(*ptr, ':');
    if (colon == NULL){
      /* PATH is empty */
      *ptr = red_known_good_path;
      red_log_error("empty path", "");
      return;
    }

    char const *ensure_path = *ptr + /* PATH= */ 5;
    if (!strncmp(ensure_path, xstr(RED_ENSURE_PATH),
          colon - ensure_path)) {
      /* ENSURE_PATH is first path in $PATH. This is the okay case. */
      return;
    }

    /* Some other directory is the first path in $PATH. Add ENSURE_PATH
     * plus a colon just after the equals sign. */
    red_log_error("malformed path", *ptr);
    int len = strlen(xstr(RED_ENSURE_PATH)) + strlen(ensure_path)
              /* PATH= */ + 5
              /* colon between first path and rest */ + 1
              /* final null byte */ + 1;
    char *tmp = (char *)malloc(len * sizeof(char));
    snprintf(tmp, len, "PATH=%s:%s", xstr(RED_ENSURE_PATH), ensure_path);
    *ptr = tmp;
    return;
  }

  red_log_error("PATH not in env!", "");
#endif /* ifdef RED_ENSURE_PATH */
}


/* this method is to write log about the process creation. */

static void red_report_call(char const *fun, char const *const argv[],
    long long timestamp) {
    if (!initialized)
        return;

    pthread_mutex_lock(&mutex);
    const char *cwd = getcwd(NULL, 0);
    if (0 == cwd) {
        perror("red: getcwd");
        exit(EXIT_FAILURE);
    }
    char const * const out_dir = initial_env[0];
    size_t const path_max_length = strlen(out_dir) + 32;
    char filename[path_max_length];
    if (-1 == snprintf(filename, path_max_length, "%s/%d.cmd", out_dir, getpid())) {
        perror("red: snprintf");
        exit(EXIT_FAILURE);
    }
    FILE * fd = fopen(filename, "a+");
    if (0 == fd) {
        perror("red: fopen");
        exit(EXIT_FAILURE);
    }
    fprintf(fd, "EXEC%c", RS);
    fprintf(fd, "%lld%c", timestamp, RS);
    fprintf(fd, "%d%c", getpid(), RS);
    fprintf(fd, "%d%c", getppid(), RS);
    fprintf(fd, "%s%c", fun, RS);
    fprintf(fd, "%s%c", cwd, RS);
    size_t const argc = red_strings_length(argv);
    for (size_t it = 0; it < argc; ++it) {
        fprintf(fd, "%s%c", argv[it], US);
    }
    fprintf(fd, "%c", GS);
    if (fclose(fd)) {
        perror("red: fclose");
        exit(EXIT_FAILURE);
    }
    free((void *)cwd);
    pthread_mutex_unlock(&mutex);
}

/* update environment assure that chilren processes will copy the desired
 * behaviour */

static int red_capture_env_t(red_env_t *env) {
    int status = 1;
    for (size_t it = 0; it < ENV_SIZE; ++it) {
        char const * const env_value = getenv(env_names[it]);
        char const * const env_copy = (env_value) ? strdup(env_value) : env_value;
        (*env)[it] = env_copy;
        status &= (env_copy) ? 1 : 0;
    }
    return status;
}

static void red_release_env_t(red_env_t *env) {
    for (size_t it = 0; it < ENV_SIZE; ++it) {
        free((void *)(*env)[it]);
        (*env)[it] = 0;
    }
}

static char const **red_update_environment(char *const envp[], red_env_t *env) {
    char const **result = red_strings_copy((char const **)envp);
    for (size_t it = 0; it < ENV_SIZE && (*env)[it]; ++it)
        result = red_update_environ(result, env_names[it], (*env)[it]);
    return result;
}

static char const **red_update_environ(char const *envs[], char const *key, char const * const value) {
    // find the key if it's there
    size_t const key_length = strlen(key);
    char const **it = envs;
    for (; (it) && (*it); ++it) {
        if ((0 == strncmp(*it, key, key_length)) &&
            (strlen(*it) > key_length) && ('=' == (*it)[key_length]))
            break;
    }
    // allocate a environment entry
    size_t const value_length = strlen(value);
    size_t const env_length = key_length + value_length + 2;
    char *env = malloc(env_length);
    if (0 == env) {
        perror("red: malloc [in env_update]");
        exit(EXIT_FAILURE);
    }
    if (-1 == snprintf(env, env_length, "%s=%s", key, value)) {
        perror("red: snprintf");
        exit(EXIT_FAILURE);
    }
    // replace or append the environment entry
    if (it && *it) {
        free((void *)*it);
        *it = env;
	return envs;
    }
    return red_strings_append(envs, env);
}

/* util methods to deal with string arrays. environment and process arguments
 * are both represented as string arrays. */

static char const **red_strings_build(char const *const arg, va_list *args) {
    char const **result = 0;
    size_t size = 0;
    for (char const *it = arg; it; it = va_arg(*args, char const *)) {
        result = realloc(result, (size + 1) * sizeof(char const *));
        if (0 == result) {
            perror("red: realloc");
            exit(EXIT_FAILURE);
        }
        char const *copy = strdup(it);
        if (0 == copy) {
            perror("red: strdup");
            exit(EXIT_FAILURE);
        }
        result[size++] = copy;
    }
    result = realloc(result, (size + 1) * sizeof(char const *));
    if (0 == result) {
        perror("red: realloc");
        exit(EXIT_FAILURE);
    }
    result[size++] = 0;

    return result;
}

static char const **red_strings_copy(char const **const in) {
    size_t const size = red_strings_length(in);

    char const **const result = malloc((size + 1) * sizeof(char const *));
    if (0 == result) {
        perror("red: malloc");
        exit(EXIT_FAILURE);
    }

    char const **out_it = result;
    for (char const *const *in_it = in; (in_it) && (*in_it);
         ++in_it, ++out_it) {
        *out_it = strdup(*in_it);
        if (0 == *out_it) {
            perror("red: strdup");
            exit(EXIT_FAILURE);
        }
    }
    *out_it = 0;
    return result;
}

static char const **red_strings_append(char const **const in,
                                        char const *const e) {
    size_t size = red_strings_length(in);
    char const **result = realloc(in, (size + 2) * sizeof(char const *));
    if (0 == result) {
        perror("red: realloc");
        exit(EXIT_FAILURE);
    }
    result[size++] = e;
    result[size++] = 0;
    return result;
}

static size_t red_strings_length(char const *const *const in) {
    size_t result = 0;
    for (char const *const *it = in; (it) && (*it); ++it)
        ++result;
    return result;
}

static void red_strings_release(char const **in) {
    for (char const *const *it = in; (it) && (*it); ++it) {
        free((void *)*it);
    }
    free((void *)in);
}
