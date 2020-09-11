// RUN: rm -rf %t.out
// RUN: mkdir -p %t.out
// RUN: clang -o %t.uninstrumented %s
// RUN: env BRABANDER_DONT_OPTIMIZE=true %brabander-clang -o %t %s
// RUN: python -c'print"A"*20' > %t.bin
// RUN: env BRABANDER_OPTIONS="brabander_file=%t.bin output_dir=%t.out" %t %t.bin
// RUN: %t.uninstrumented %t.bin | FileCheck --check-prefix=CHECK-ORIG %s
// RUN: %t.uninstrumented %t.out/id-0-0-0 | FileCheck --check-prefix=CHECK-GEN %s

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main (int argc, char** argv) {
  if (argc < 2) {
    fprintf(stderr, "Usage: %s [file]\n", argv[0]);
    return -1;
  }

  char buf[20], copy[20];
  size_t ret;

  FILE* fp = fopen(argv[1], "rb");

  if (!fp) {
    fprintf(stderr, "Failed to open\n");
    return -1;
  }

  if (fread(buf, 1, sizeof(buf), fp) != sizeof(buf)) {
    fprintf(stderr, "Failed to read\n");
    return -1;
  }

  fclose(fp);

  memcpy(copy, buf, sizeof(buf));
  copy[3] = 0x80;

  if (buf[0] != 0x80
      && *(int*)copy == 0x80adbeef) {
    // CHECK-GEN: Good
    printf("Good\n");
  }
  else {
    // CHECK-ORIG: Bad
    printf("Bad\n");
  }
}
