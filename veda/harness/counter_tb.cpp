// Verilator leg of the differential harness for designs/counter.
// Reads "rst en" lines; prints the count output sampled before each
// posedge (matching the Lean interpreter's Mealy convention and the
// arcilator testbench's clk-low sampling).
#include "Vcounter.h"
#include "verilated.h"
#include <cstdio>

int main(int argc, char **argv) {
  if (argc < 2) {
    fprintf(stderr, "usage: %s <stim.txt>\n", argv[0]);
    return 1;
  }
  FILE *f = fopen(argv[1], "r");
  if (!f) {
    fprintf(stderr, "cannot open %s\n", argv[1]);
    return 1;
  }
  VerilatedContext ctx;
  Vcounter top(&ctx);
  int rst, en;
  top.clk = 0;
  while (fscanf(f, "%d %d", &rst, &en) == 2) {
    top.rst = rst;
    top.en = en;
    top.eval();
    printf("%d\n", (int)top.count);
    top.clk = 1;
    top.eval();
    top.clk = 0;
    top.eval();
  }
  fclose(f);
  return 0;
}
