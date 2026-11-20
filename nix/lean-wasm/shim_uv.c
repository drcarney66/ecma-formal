// Emscripten's single-threaded libc lacks pthread_setname_np, which libuv's thread.c calls.
#include <pthread.h>
int pthread_setname_np(pthread_t t, const char* n) {
  (void)t;
  (void)n;
  return 0;
}
