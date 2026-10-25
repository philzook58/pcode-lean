/* Native calls execute the exact instructions used to produce the Lean fixtures.
   The inline wrapper captures flags before C code can overwrite them. */
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

uint64_t inc64(uint64_t, uint64_t);
uint64_t umax64(uint64_t, uint64_t);
uint64_t count64(uint64_t, uint64_t);
uint64_t afgap64(uint64_t, uint64_t);
uint64_t alias64(uint64_t, uint64_t);
uint64_t stack64(uint64_t, uint64_t);
uint64_t shift64(uint64_t, uint64_t);

int main(int argc, char **argv) {
  if (argc != 2) return 2;
  uint64_t (*fn)(uint64_t, uint64_t) = NULL;
  if (!strcmp(argv[1], "inc")) fn = inc64;
  if (!strcmp(argv[1], "max")) fn = umax64;
  if (!strcmp(argv[1], "count")) fn = count64;
  if (!strcmp(argv[1], "afgap")) fn = afgap64;
  if (!strcmp(argv[1], "alias")) fn = alias64;
  if (!strcmp(argv[1], "stack")) fn = stack64;
  if (!strcmp(argv[1], "shift")) fn = shift64;
  if (!fn) return 2;
  uint64_t a, b;
  while (scanf("%" SCNu64 " %" SCNu64, &a, &b) == 2) {
    uint64_t result, flags;
    __asm__ volatile ("call *%[function]\n\tpushfq\n\tpop %[flags]"
      : "=&a"(result), [flags] "=&r"(flags), "+D"(a), "+S"(b)
      : [function] "r"(fn)
      : "rcx", "rdx", "r8", "r9", "r10", "r11", "cc", "memory");
    printf("%" PRIu64 " %" PRIu64 "\n", result, flags);
  }
  return 0;
}
