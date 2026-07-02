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

src=$(realpath "$1")
outdir=$(realpath "${2:-$(dirname "$src")}")
name=$(basename "$src" .sv)

# Run from the output directory on basenames so that source locations
# embedded in the IR (e.g. hw.module result_locs) are stable regardless of
# the caller's working directory — the generic MLIR is checked into git and
# CI diffs it against a regeneration.
cd "$outdir"
cp -f "$src" "./$name.sv" 2>/dev/null || true
circt-verilog --ir-hw "$name.sv" -o "$name.hw.mlir"
circt-opt --mlir-print-op-generic "$name.hw.mlir" -o "$name.generic.mlir"
echo "wrote $outdir/$name.hw.mlir and $outdir/$name.generic.mlir"
