#!/usr/bin/env bash
# Canonical SystemVerilog -> MLIR import pipeline for Veda.
#
# Usage: bridge/import.sh <design.sv> [outdir]
#
# Produces, next to the input (or in [outdir]):
#   <name>.hw.mlir       - hw/comb/seq pretty form (human review)
#   <name>.generic.mlir  - generic op form (what Veda/Import parses)
#
# Requires circt-verilog and circt-opt from the pinned CIRCT release
# (see veda/toolchain.lock) on PATH.
set -euo pipefail

src=$1
outdir=${2:-$(dirname "$src")}
name=$(basename "$src" .sv)

circt-verilog --ir-hw "$src" -o "$outdir/$name.hw.mlir"
circt-opt --mlir-print-op-generic "$outdir/$name.hw.mlir" -o "$outdir/$name.generic.mlir"
echo "wrote $outdir/$name.hw.mlir and $outdir/$name.generic.mlir"
