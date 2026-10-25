/* Original native oracle for the scan and two-limb addition examples. */
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
uint64_t scan64(uint64_t, const uint64_t *);
int main(void) {
  char kind[16];
  while (scanf("%15s", kind) == 1) {
    if (!strcmp(kind, "scan")) {
      unsigned n;
      uint64_t words[64];
      if (scanf("%u", &n) != 1 || n > 64) return 2;
      for (unsigned i = 0; i < n; ++i)
        if (scanf("%" SCNu64, &words[i]) != 1) return 2;
      printf("%" PRIu64 "\n", scan64(n, words));
    } else if (!strcmp(kind, "add")) {
      uint64_t a, b, c, d, lo, flags;
      if (scanf("%" SCNu64 " %" SCNu64 " %" SCNu64 " %" SCNu64, &a,&b,&c,&d) != 4) return 2;
      __asm__ volatile ("call add128\n\tpushfq\n\tpop %[flags]"
        : "=&a"(lo), "+D"(a), "+S"(b), "+d"(c), "+c"(d), [flags] "=&r"(flags)
        : : "r8", "r9", "r10", "r11", "cc", "memory");
      printf("%" PRIu64 " %" PRIu64 " %" PRIu64 "\n", lo, c, flags & 1);
    } else return 2;
  }
  return 0;
}
